/**
 * @file schema_mount.c
 * @author Tadeas Vintrlik <xvintr04@stud.fit.vutbr.cz>
 * @brief libyang extension plugin - Schema Mount (RFC 8528)
 *
 * Copyright (c) 2021 CESNET, z.s.p.o.
 *
 * This source code is licensed under BSD 3-Clause License (the "License").
 * You may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     https://opensource.org/licenses/BSD-3-Clause
 */

#define _GNU_SOURCE

#include <assert.h>
#include <pthread.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "dict.h"
#include "libyang.h"
#include "log.h"
#include "plugins_exts.h"
#include "tree_data.h"
#include "tree_schema.h"

/**
 * @brief Internal schema mount data structure for holding all the contexts of parsed data.
 */
struct lyplg_ext_sm {
    struct lyplg_ext_sm_shared {
        pthread_mutex_t lock;           /**< lock for accessing this shared structure */

        struct {
            struct ly_ctx *ctx;         /**< context shared between all data of this mount point */
            const char *mount_point;    /**< mount point name */
            const char *content_id;     /**< yang-library content-id (alternatively module-set-id),
                                             stored in the dictionary of the ext instance context */
        } *schemas;                     /**< array of shared schema schemas */
        uint32_t schema_count;          /**< length of schemas array */
        uint32_t ref_count;             /**< number of references to this structure (mount-points with the same name
                                             in the module) */
    } *shared;                          /**< shared schema mount points */

    struct lyplg_ext_sm_inln {
        struct {
            struct ly_ctx *ctx;         /**< context created for single inline schema data */
        } *schemas;                     /**< array of inline schemas */
        uint32_t schema_count;          /**< length of schemas array */
    } inln;                             /**< inline mount points */
};

#define EXT_LOGERR_MEM_RET(ext) \
        lyplg_ext_log(ext, LY_LLERR, LY_EMEM, NULL, "Memory allocation failed (%s:%d).", __FILE__, __LINE__); \
        return LY_EMEM

#define EXT_LOGERR_MEM_GOTO(ext, rc, label) \
        lyplg_ext_log(ext, LY_LLERR, LY_EMEM, NULL, "Memory allocation failed (%s:%d).", __FILE__, __LINE__); \
        rc = LY_EMEM; \
        goto label

#define EXT_LOGERR_INT_RET(ext) \
        lyplg_ext_log(ext, LY_LLERR, LY_EINT, NULL, "Internal error (%s:%d).", __FILE__, __LINE__); \
        return LY_EINT

/**
 * @brief Check if given mount point is unique among its' siblings
 *
 * @param cctx Compilation context.
 * @param c_ext Compiled extension instance for checking uniqueness.
 * @param p_ext Extension instance of the mount-point for comparison.
 * @return LY_SUCCESS if is unique;
 * @return LY_EINVAL otherwise.
 */
static LY_ERR
schema_mount_compile_unique_mp(struct lysc_ctx *cctx, const struct lysc_ext_instance *c_ext,
        const struct lysp_ext_instance *p_ext)
{
    struct lysc_ext_instance *exts;
    LY_ARRAY_COUNT_TYPE u;
    struct lysc_node *parent;

    /* check if it is the only instance of the mount-point among its' siblings */
    parent = (struct lysc_node *)c_ext->parent;
    exts = parent->exts;
    LY_ARRAY_FOR(exts, u) {
        if (&exts[u] == c_ext) {
            continue;
        }

        if (!strcmp(exts[u].def->module->name, "ietf-yang-schema-mount") && !strcmp(exts[u].def->name, "mount-point")) {
            lyplg_ext_log(c_ext, LY_LLERR, LY_EVALID, lysc_ctx_get_path(cctx), "Multiple extension \"%s\" instances.",
                    p_ext->name);
            return LY_EINVAL;
        }
    }
    return LY_SUCCESS;
}

struct lyplg_ext_sm_shared_cb_data {
    const struct lysc_ext_instance *ext;
    struct lyplg_ext_sm_shared *sm_shared;
};

static LY_ERR
schema_mount_compile_mod_dfs_cb(struct lysc_node *node, void *data, ly_bool *dfs_continue)
{
    struct lyplg_ext_sm_shared_cb_data *cb_data = data;
    struct lyplg_ext_sm *sm_data;
    struct lysc_ext_instance *exts;
    LY_ARRAY_COUNT_TYPE u;

    (void)dfs_continue;

    if (node == cb_data->ext->parent) {
        /* parent of the current compiled extension, skip */
        return LY_SUCCESS;
    }

    /* find the same mount point */
    exts = node->exts;
    LY_ARRAY_FOR(exts, u) {
        if (!strcmp(exts[u].def->module->name, "ietf-yang-schema-mount") && !strcmp(exts[u].def->name, "mount-point") &&
                (exts[u].argument == cb_data->ext->argument)) {
            /* same mount point, break the DFS search */
            sm_data = exts[u].data;
            cb_data->sm_shared = sm_data->shared;
            return LY_EEXIST;
        }
    }

    /* not found, continue search */
    return LY_SUCCESS;
}

static struct lyplg_ext_sm_shared *
schema_mount_compile_find_shared(const struct lys_module *mod, const struct lysc_ext_instance *ext)
{
    struct lyplg_ext_sm_shared_cb_data cb_data;
    LY_ERR r;

    /* prepare cb_data */
    cb_data.ext = ext;
    cb_data.sm_shared = NULL;

    /* try to find the same mount point */
    r = lysc_module_dfs_full(mod, schema_mount_compile_mod_dfs_cb, &cb_data);
    assert((!r && !cb_data.sm_shared) || ((r == LY_EEXIST) && cb_data.sm_shared));

    return cb_data.sm_shared;
}

/**
 * @brief Schema mount compile.
 * Checks if it can be a valid extension instance for yang schema mount.
 *
 * Implementation of ::lyplg_ext_compile_clb callback set as lyext_plugin::compile.
 */
static LY_ERR
schema_mount_compile(struct lysc_ctx *cctx, const struct lysp_ext_instance *p_ext, struct lysc_ext_instance *c_ext)
{
    const struct lys_module *cur_mod;
    struct lyplg_ext_sm *sm_data;

    assert(!strcmp(p_ext->name, "yangmnt:mount-point"));

    /* check YANG version 1.1 */
    cur_mod = lysc_ctx_get_cur_mod(cctx);
    if (cur_mod->parsed->version != LYS_VERSION_1_1) {
        lyplg_ext_log(c_ext, LY_LLERR, LY_EVALID, lysc_ctx_get_path(cctx),
                "Extension \"%s\" instance not allowed in YANG version 1 module.", p_ext->name);
        return LY_EINVAL;
    }

    /* check parent nodetype */
    if ((p_ext->parent_stmt != LY_STMT_CONTAINER) && (p_ext->parent_stmt != LY_STMT_LIST)) {
        lyplg_ext_log(c_ext, LY_LLERR, LY_EVALID, lysc_ctx_get_path(cctx),
                "Extension \"%s\" instance allowed only in container or list statement.", p_ext->name);
        return LY_EINVAL;
    }

    /* check uniqueness */
    if (schema_mount_compile_unique_mp(cctx, c_ext, p_ext)) {
        return LY_EINVAL;
    }

    /* init internal data */
    sm_data = calloc(1, sizeof *sm_data);
    if (!sm_data) {
        EXT_LOGERR_MEM_RET(c_ext);
    }
    c_ext->data = sm_data;

    /* reuse/init shared schema */
    sm_data->shared = schema_mount_compile_find_shared(c_ext->module, c_ext);
    if (sm_data->shared) {
        ++sm_data->shared->ref_count;
    } else {
        sm_data->shared = calloc(1, sizeof *sm_data->shared);
        if (!sm_data->shared) {
            free(sm_data);
            EXT_LOGERR_MEM_RET(c_ext);
        }
        pthread_mutex_init(&sm_data->shared->lock, NULL);
        sm_data->shared->ref_count = 1;
    }

    return LY_SUCCESS;
}

/**
 * @brief Learn details about the current mount point.
 *
 * @param[in] ext Compiled extension instance.
 * @param[in] ext_data Extension data retrieved by the callback.
 * @param[out] config Whether the whole schema should keep its config or be set to false.
 * @param[out] shared Whether the schema is shared or inline.
 * @return LY_ERR value.
 */
static LY_ERR
schema_mount_get_smount(const struct lysc_ext_instance *ext, const struct lyd_node *ext_data, ly_bool *config,
        ly_bool *shared)
{
    struct lyd_node *mpoint, *node;
    char *path = NULL;
    LY_ERR r;

    /* find the mount point */
    if (asprintf(&path, "/ietf-yang-schema-mount:schema-mounts/mount-point[module='%s'][label='%s']", ext->module->name,
            ext->argument) == -1) {
        EXT_LOGERR_MEM_RET(ext);
    }
    r = ext_data ? lyd_find_path(ext_data, path, 0, &mpoint) : LY_ENOTFOUND;
    free(path);
    if (r) {
        /* missing mount-point, cannot be data for this extension (https://datatracker.ietf.org/doc/html/rfc8528#page-10) */
        return LY_ENOT;
    }

    /* check config */
    if (!lyd_find_path(mpoint, "config", 0, &node) && !strcmp(lyd_get_value(node), "false")) {
        *config = 0;
    } else {
        *config = 1;
    }

    /* check schema-ref */
    if (lyd_find_path(mpoint, "shared-schema", 0, NULL)) {
        if (lyd_find_path(mpoint, "inline", 0, NULL)) {
            EXT_LOGERR_INT_RET(ext);
        }
        *shared = 0;
    } else {
        *shared = 1;
    }

    return LY_SUCCESS;
}

/**
 * @brief Create schema (context) based on retrieved extension data.
 *
 * @param[in] ext Compiled extension instance.
 * @param[in] ext_data Extension data retrieved by the callback.
 * @param[in] config Whether the whole schema should keep its config or be set to false.
 * @param[out] ext_ctx Schema to use for parsing the data.
 * @return LY_ERR value.
 */
static LY_ERR
schema_mount_create_ctx(const struct lysc_ext_instance *ext, const struct lyd_node *ext_data, ly_bool config,
        struct ly_ctx **ext_ctx)
{
    LY_ERR r;
    const char * const *searchdirs;
    const struct lys_module *mod;
    struct lysc_node *root, *node;
    uint32_t idx = 0;

    /* get searchdirs from the current context */
    searchdirs = ly_ctx_get_searchdirs(ext->module->ctx);

    /* create the context based on the data */
    if ((r = ly_ctx_new_yldata(searchdirs ? searchdirs[0] : NULL, ext_data, ly_ctx_get_options(ext->module->ctx), ext_ctx))) {
        lyplg_ext_log(ext, LY_LLERR, r, NULL, "Failed to create context for the schema-mount data.");
        return r;
    }

    if (!config) {
        /* manually change the config of all schema nodes in all the modules */
        while ((mod = ly_ctx_get_module_iter(*ext_ctx, &idx))) {
            if (!mod->implemented) {
                continue;
            }

            LY_LIST_FOR(mod->compiled->data, root) {
                LYSC_TREE_DFS_BEGIN(root, node) {
                    node->flags &= ~LYS_CONFIG_W;
                    node->flags |= LYS_CONFIG_R;

                    LYSC_TREE_DFS_END(root, node);
                }
            }
        }
    }

    return LY_SUCCESS;
}

/**
 * @brief Get schema (context) for a shared-schema mount point.
 *
 * @param[in] ext Compiled extension instance.
 * @param[in] ext_data Extension data retrieved by the callback.
 * @param[in] config Whether the whole schema should keep its config or be set to false.
 * @param[out] ext_ctx Schema to use for parsing the data.
 * @return LY_ERR value.
 */
static LY_ERR
schema_mount_get_ctx_shared(struct lysc_ext_instance *ext, const struct lyd_node *ext_data, ly_bool config,
        const struct ly_ctx **ext_ctx)
{
    struct lyplg_ext_sm *sm_data = ext->data;
    LY_ERR ret = LY_SUCCESS, r;
    struct lyd_node *node = NULL;
    struct ly_ctx *new_ctx;
    uint32_t i;
    const char *content_id = NULL;
    void *mem;

    assert(sm_data && sm_data->shared);

    /* get yang-library content-id or module-set-id */
    if (ext_data) {
        lyd_find_path(ext_data, "/ietf-yang-library:yang-library/content-id", 0, &node);
        if (!node) {
            lyd_find_path(ext_data, "/ietf-yang-library:modules-state/module-set-id", 0, &node);
        }
        if (node) {
            content_id = lyd_get_value(node);
        }
    }
    if (!content_id) {
        lyplg_ext_log(ext, LY_LLERR, LY_EVALID, NULL, "Missing \"content-id\" or \"module-set-id\" in ietf-yang-library data.");
        return LY_EVALID;
    }

    /* LOCK */
    if ((r = pthread_mutex_lock(&sm_data->shared->lock))) {
        lyplg_ext_log(ext, LY_LLERR, LY_ESYS, NULL, "Mutex lock failed (%s).", strerror(r));
        return LY_ESYS;
    }

    /* try to find this mount point */
    for (i = 0; i < sm_data->shared->schema_count; ++i) {
        if (ext->argument == sm_data->shared->schemas[i].mount_point) {
            break;
        }
    }

    if (i < sm_data->shared->schema_count) {
        /* schema exists already */
        if (strcmp(content_id, sm_data->shared->schemas[i].content_id)) {
            lyplg_ext_log(ext, LY_LLERR, LY_EVALID, "/ietf-yang-library:yang-library/content-id",
                    "Shared-schema yang-library content-id \"%s\" differs from \"%s\" used previously.",
                    content_id, sm_data->shared->schemas[i].content_id);
            ret = LY_EVALID;
            goto cleanup;
        }
    } else {
        /* no schema found, create it */
        if ((r = schema_mount_create_ctx(ext, ext_data, config, &new_ctx))) {
            ret = r;
            goto cleanup;
        }

        /* new entry */
        mem = realloc(sm_data->shared->schemas, (i + 1) * sizeof *sm_data->shared->schemas);
        if (!mem) {
            ly_ctx_destroy(new_ctx);
            EXT_LOGERR_MEM_GOTO(ext, ret, cleanup);
        }
        sm_data->shared->schemas = mem;
        ++sm_data->shared->schema_count;

        /* fill entry */
        sm_data->shared->schemas[i].ctx = new_ctx;
        sm_data->shared->schemas[i].mount_point = ext->argument;
        lydict_insert(ext->module->ctx, content_id, 0, &sm_data->shared->schemas[i].content_id);
    }

    /* use the context */
    *ext_ctx = sm_data->shared->schemas[i].ctx;

cleanup:
    /* UNLOCK */
    pthread_mutex_unlock(&sm_data->shared->lock);

    return ret;
}

/**
 * @brief Get schema (context) for an inline mount point.
 *
 * @param[in] ext Compiled extension instance.
 * @param[in] ext_data Extension data retrieved by the callback.
 * @param[in] config Whether the whole schema should keep its config or be set to false.
 * @param[out] ext_ctx Schema to use for parsing the data.
 * @return LY_ERR value.
 */
static LY_ERR
schema_mount_get_ctx_inline(struct lysc_ext_instance *ext, const struct lyd_node *ext_data, ly_bool config,
        const struct ly_ctx **ext_ctx)
{
    struct lyplg_ext_sm *sm_data = ext->data;
    LY_ERR r;
    struct ly_ctx *new_ctx;
    uint32_t i;
    void *mem;

    assert(sm_data && sm_data->shared);

    i = sm_data->inln.schema_count;

    /* always new schema required, create context */
    if ((r = schema_mount_create_ctx(ext, ext_data, config, &new_ctx))) {
        return r;
    }

    /* new entry */
    mem = realloc(sm_data->inln.schemas, (i + 1) * sizeof *sm_data->inln.schemas);
    if (!mem) {
        ly_ctx_destroy(new_ctx);
        EXT_LOGERR_MEM_RET(ext);
    }
    sm_data->inln.schemas = mem;
    ++sm_data->inln.schema_count;

    /* fill entry */
    sm_data->inln.schemas[i].ctx = new_ctx;

    /* use the context */
    *ext_ctx = sm_data->inln.schemas[i].ctx;
    return LY_SUCCESS;
}

/**
 * @brief Get schema (context) for a mount point.
 *
 * @param[in] ext Compiled extension instance.
 * @param[out] ext_ctx Schema to use for parsing the data.
 * @return LY_ERR value.
 */
static LY_ERR
schema_mount_get_ctx(struct lysc_ext_instance *ext, const struct ly_ctx **ext_ctx)
{
    LY_ERR ret = LY_SUCCESS, r;
    struct lyd_node *iter, *ext_data = NULL;
    ly_bool ext_data_free = 0, config, shared;

    *ext_ctx = NULL;

    /* get operational data with ietf-yang-library and ietf-yang-schema-mount data */
    if ((r = lyplg_ext_get_data(ext->module->ctx, ext, (void **)&ext_data, &ext_data_free))) {
        ret = r;
        goto cleanup;
    }

    LY_LIST_FOR(ext_data, iter) {
        if (iter->flags & LYD_NEW) {
            /* must be validated for the parent-reference prefix data to be stored */
            lyplg_ext_log(ext, LY_LLERR, LY_EINVAL, NULL, "Provided ext data have not been validated.");
            ret = LY_EINVAL;
            goto cleanup;
        }
    }

    /* learn about this mount point */
    if ((r = schema_mount_get_smount(ext, ext_data, &config, &shared))) {
        ret = r;
        goto cleanup;
    }

    /* create/get the context for parsing the data */
    if (shared) {
        r = schema_mount_get_ctx_shared(ext, ext_data, config, ext_ctx);
    } else {
        r = schema_mount_get_ctx_inline(ext, ext_data, config, ext_ctx);
    }
    if (r) {
        ret = r;
        goto cleanup;
    }

cleanup:
    if (ext_data_free) {
        lyd_free_all(ext_data);
    }
    return ret;
}

/**
 * @brief Parse callback for schema mount.
 * Check if data if valid for schema mount and inserts it to the parent.
 */
static LY_ERR
schema_mount_parse(struct ly_in *in, LYD_FORMAT format, struct lysc_ext_instance *ext, struct lyd_node *parent,
        uint32_t parse_opts)
{
    LY_ERR ret = LY_SUCCESS, r;
    const struct ly_ctx *ext_ctx;
    struct lyd_node *subtree, *first = NULL;
    struct ly_err_item *err;
    uint32_t old_log_opts;

    /* get context based on ietf-yang-library data */
    if ((r = schema_mount_get_ctx(ext, &ext_ctx))) {
        return r;
    }

    /* prepare opts */
    old_log_opts = ly_log_options(LY_LOSTORE_LAST);
    assert(parse_opts & LYD_PARSE_ONLY);
    parse_opts |= LYD_PARSE_SUBTREE;

    do {
        /* parse by nested subtrees */
        r = lyd_parse_data(ext_ctx, NULL, in, format, parse_opts, 0, &subtree);
        if (r && (r != LY_ENOT)) {
            /* error, maybe valid, maybe not, print as verbose */
            err = ly_err_first(ext_ctx);
            if (!err) {
                lyplg_ext_log(ext, LY_LLVRB, 0, NULL, "Unknown parsing error (err code %d).", r);
            } else {
                lyplg_ext_log(ext, LY_LLVRB, 0, NULL, "%s (err code %d).", err->msg, err->no);
            }
            ret = LY_ENOT;
            goto cleanup;
        }

        /* set the special flag and insert into siblings */
        subtree->flags |= LYD_EXT;
        lyd_insert_sibling(first, subtree, &first);
    } while (r == LY_ENOT);

    /* append to parent */
    if (first && (r = lyd_insert_ext(parent, first))) {
        lyplg_ext_log(ext, LY_LLERR, r, NULL, "Failed to append parsed data.");
        ret = r;
        goto cleanup;
    }

cleanup:
    ly_log_options(old_log_opts);
    if (ret) {
        lyd_free_siblings(first);
    }
    return ret;
}

/**
 * @brief Duplicate all accessible parent references for a shared-schema mount point.
 *
 * @param[in] ext Compiled extension instance.
 * @param[in] ctx_node Context node for evaluating the parent-reference XPath expressions.
 * @param[in] ext_data Extension data retrieved by the callback.
 * @param[in] trg_ctx Mounted data context to use for duplication.
 * @param[out] ref_set Set of all top-level parent-ref subtrees connected to each other, may be empty.
 * @return LY_ERR value.
 */
static LY_ERR
schema_mount_dup_parent_ref(const struct lysc_ext_instance *ext, const struct lyd_node *ctx_node,
        const struct lyd_node *ext_data, const struct ly_ctx *trg_ctx, struct ly_set **ref_set)
{
    LY_ERR ret = LY_SUCCESS;
    char *path = NULL;
    struct ly_set *set = NULL, *par_set = NULL;
    struct lyd_node_term *term;
    struct lyd_node *dup = NULL, *top_node, *first;
    struct lyd_value_xpath10 *xp_val;
    uint32_t i, j;

    *ref_set = NULL;

    if (!ext_data) {
        /* we expect the same ext data as before and there must be some for data to be parsed */
        lyplg_ext_log(ext, LY_LLERR, LY_EINVAL, NULL, "No ext data provided.");
        ret = LY_EINVAL;
        goto cleanup;
    }

    /* get all parent references of this mount point */
    if (asprintf(&path, "/ietf-yang-schema-mount:schema-mounts/mount-point[module='%s'][label='%s']"
            "/shared-schema/parent-reference", ext->module->name, ext->argument) == -1) {
        EXT_LOGERR_MEM_GOTO(ext, ret, cleanup);
    }
    if ((ret = lyd_find_xpath(ext_data, path, &set))) {
        goto cleanup;
    }

    /* prepare result set */
    if ((ret = ly_set_new(ref_set))) {
        goto cleanup;
    }

    first = NULL;
    for (i = 0; i < set->count; ++i) {
        term = set->objs[i];

        /* get the referenced nodes (subtrees) */
        LYD_VALUE_GET(&term->value, xp_val);
        if ((ret = lyd_find_xpath4(ctx_node, ctx_node, lyxp_get_expr(xp_val->exp), xp_val->format, xp_val->prefix_data,
                NULL, &par_set))) {
            goto cleanup;
        }

        for (j = 0; j < par_set->count; ++j) {
            /* duplicate with parents in the context of the mounted data */
            if ((ret = lyd_dup_single_to_ctx(par_set->dnodes[j], trg_ctx, NULL,
                    LYD_DUP_RECURSIVE | LYD_DUP_WITH_PARENTS | LYD_DUP_WITH_FLAGS, &dup))) {
                goto cleanup;
            }

            /* go top-level */
            while (dup->parent) {
                dup = lyd_parent(dup);
            }

            /* check whether the top-level node exists */
            if (first) {
                if ((ret = lyd_find_sibling_first(first, dup, &top_node)) && (ret != LY_ENOTFOUND)) {
                    goto cleanup;
                }
            } else {
                top_node = NULL;
            }

            if (top_node) {
                /* merge */
                ret = lyd_merge_tree(&first, dup, LYD_MERGE_DESTRUCT);
                dup = NULL;
                if (ret) {
                    goto cleanup;
                }
            } else {
                /* insert */
                if ((ret = lyd_insert_sibling(first, dup, &first))) {
                    goto cleanup;
                }

                /* add into the result set because a new top-level node was added */
                if ((ret = ly_set_add(*ref_set, dup, 1, NULL))) {
                    goto cleanup;
                }
                dup = NULL;
            }
        }
    }

cleanup:
    free(path);
    ly_set_free(set, NULL);
    ly_set_free(par_set, NULL);
    lyd_free_tree(dup);
    if (ret && *ref_set) {
        if ((*ref_set)->count) {
            lyd_free_siblings((*ref_set)->dnodes[0]);
        }
        ly_set_free(*ref_set, NULL);
        *ref_set = NULL;
    }
    return ret;
}

/**
 * @brief Validate callback for schema mount.
 */
static LY_ERR
schema_mount_validate(struct lysc_ext_instance *ext, struct lyd_node *sibling, uint32_t val_opts)
{
    LY_ERR ret = LY_SUCCESS;
    uint32_t old_log_opts, i;
    struct ly_err_item *err;
    struct lyd_node *iter, *ext_data = NULL, *ref_first = NULL, *orig_parent = lyd_parent(sibling);
    ly_bool ext_data_free = 0;
    struct ly_set *ref_set = NULL;

    if (!sibling) {
        /* some data had to be parsed for this callback to be called */
        EXT_LOGERR_INT_RET(ext);
    }

    /* get operational data with ietf-yang-library and ietf-yang-schema-mount data */
    if ((ret = lyplg_ext_get_data(ext->module->ctx, ext, (void **)&ext_data, &ext_data_free))) {
        goto cleanup;
    }

    LY_LIST_FOR(ext_data, iter) {
        if (iter->flags & LYD_NEW) {
            /* must be validated for the parent-reference prefix data to be stored */
            lyplg_ext_log(ext, LY_LLERR, LY_EINVAL, NULL, "Provided ext data have not been validated.");
            ret = LY_EINVAL;
            goto cleanup;
        }
    }

    /* duplicate the referenced parent nodes into ext context */
    if ((ret = schema_mount_dup_parent_ref(ext, orig_parent, ext_data, LYD_CTX(sibling), &ref_set))) {
        goto cleanup;
    }

    /* create accessible tree, remove LYD_EXT to not call this callback recursively */
    lyd_unlink_siblings(sibling);
    LY_LIST_FOR(sibling, iter) {
        iter->flags &= ~LYD_EXT;
    }
    if (ref_set->count) {
        if ((ret = lyd_insert_sibling(sibling, ref_set->dnodes[0], &sibling))) {
            goto cleanup;
        }
    }

    /* only store messages in the context, log as an extension */
    old_log_opts = ly_log_options(LY_LOSTORE_LAST);

    /* validate all the data */
    ret = lyd_validate_all(&sibling, NULL, val_opts, NULL);
    ly_log_options(old_log_opts);

    /* restore sibling tree */
    for (i = 0; i < ref_set->count; ++i) {
        if (ref_set->dnodes[i] == sibling) {
            sibling = sibling->next;
        }
        lyd_free_tree(ref_set->dnodes[i]);
    }
    LY_LIST_FOR(sibling, iter) {
        iter->flags |= LYD_EXT;
    }
    lyd_insert_ext(orig_parent, sibling);

    if (ret) {
        /* log the error in the original context */
        err = ly_err_first(LYD_CTX(sibling));
        if (!err) {
            lyplg_ext_log(ext, LY_LLERR, ret, NULL, "Unknown validation error (err code %d).", ret);
        } else {
            lyplg_ext_log(ext, LY_LLERR, err->no, err->path, "%s", err->msg);
        }
        goto cleanup;
    }

cleanup:
    ly_set_free(ref_set, NULL);
    lyd_free_siblings(ref_first);
    if (ext_data_free) {
        lyd_free_all(ext_data);
    }
    return ret;
}

/**
 * @brief Schema mount free.
 *
 * Implementation of ::lyplg_ext_free_clb callback set as ::lyext_plugin::free.
 */
static void
schema_mount_free(struct ly_ctx *ctx, struct lysc_ext_instance *ext)
{
    struct lyplg_ext_sm *sm_data = ext->data;
    uint32_t i;

    if (!sm_data) {
        return;
    }

    if (!--sm_data->shared->ref_count) {
        for (i = 0; i < sm_data->shared->schema_count; ++i) {
            ly_ctx_destroy(sm_data->shared->schemas[i].ctx);
            lydict_remove(ctx, sm_data->shared->schemas[i].content_id);
        }
        free(sm_data->shared->schemas);
        pthread_mutex_destroy(&sm_data->shared->lock);
        free(sm_data->shared);
    }

    for (i = 0; i < sm_data->inln.schema_count; ++i) {
        ly_ctx_destroy(sm_data->inln.schemas[i].ctx);
    }
    free(sm_data->inln.schemas);
    free(sm_data);
}

/**
 * @brief Plugin descriptions for the Yang Schema Mount extension.
 *
 * Note that external plugins are supposed to use:
 *
 *   LYPLG_EXTENSIONS = {
 */
const struct lyplg_ext_record plugins_schema_mount[] = {
    {
        .module = "ietf-yang-schema-mount",
        .revision = "2019-01-14",
        .name = "mount-point",

        .plugin.id = "libyang 2 - Schema Mount, version 1",
        .plugin.compile = &schema_mount_compile,
        .plugin.sprinter = NULL,
        .plugin.free = &schema_mount_free,
        .plugin.parse = &schema_mount_parse,
        .plugin.validate = &schema_mount_validate
    },
    {0} /* terminating zeroed item */
};
