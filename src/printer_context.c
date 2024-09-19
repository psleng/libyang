/**
 * @file printer_context.c
 * @author Michal Vasko <mvasko@cesnet.cz>
 * @brief Compiled context printer
 *
 * Copyright (c) 2024 CESNET, z.s.p.o.
 *
 * This source code is licensed under BSD 3-Clause License (the "License").
 * You may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     https://opensource.org/licenses/BSD-3-Clause
 */

#include <assert.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "hash_table_internal.h"
#include "log.h"
#include "ly_common.h"
#include "plugins_exts.h"
#include "xpath.h"

static void
ctxs_dict_ht(const struct ly_ht *ht, int *size)
{
    uint32_t i, j;
    struct ly_ht_rec *rec;
    struct ly_dict_rec *dict_rec;

    /* hash table */
    *size += sizeof *ht;

    /* hlists */
    *size += ht->size * sizeof *ht->hlists;

    /* records (with string pointers) */
    *size += ht->size * ht->rec_size;

    LYHT_ITER_ALL_RECS(ht, i, j, rec) {
        dict_rec = (struct ly_dict_rec *)&rec->val;

        /* strings */
        *size += strlen(dict_rec->value) + 1;
    }
}

static void
ctxs_exts(const struct lysc_ext_instance *exts, int *size)
{
    LY_ARRAY_COUNT_TYPE u;

    /* sized array */
    *size += sizeof(LY_ARRAY_COUNT_TYPE) + LY_ARRAY_COUNT(exts) * sizeof *exts;

    LY_ARRAY_FOR(exts, u) {
        ctxs_exts(exts[u].exts, size);

        /* substms, compiled */
        if (exts[u].def->plugin && exts[u].def->plugin->compiled_size) {
            *size += exts[u].def->plugin->compiled_size(&exts[u]);
        }
    }
}

static void
ctxs_prefixes(const struct lysc_prefix *prefixes, int *size)
{
    LY_ARRAY_COUNT_TYPE u;

    *size += sizeof(LY_ARRAY_COUNT_TYPE) + LY_ARRAY_COUNT(prefixes) * sizeof *prefixes;
    LY_ARRAY_FOR(prefixes, u) {
        /* string not in the dictionary */
        *size += strlen(prefixes[u].prefix) + 1;
    }
}

static void
ctxs_expr(const struct lyxp_expr *exp, int *size)
{
    uint32_t i, j;

    *size += exp->used * sizeof *exp->tokens;
    *size += exp->used * sizeof *exp->tok_pos;
    *size += exp->used * sizeof *exp->tok_len;
    *size += exp->used * sizeof *exp->repeat;
    for (i = 0; i < exp->used; ++i) {
        if (!exp->repeat[i]) {
            continue;
        }

        for (j = 0; exp->repeat[j]; ++j) { }
        *size += (j + 1) * sizeof **exp->repeat;
    }
}

static void
ctxs_musts(const struct lysc_must *musts, int *size)
{
    LY_ARRAY_COUNT_TYPE u;

    *size += sizeof(LY_ARRAY_COUNT_TYPE) + LY_ARRAY_COUNT(musts) * sizeof *musts;
    LY_ARRAY_FOR(musts, u) {
        ctxs_expr(musts[u].cond, size);
        ctxs_prefixes(musts[u].prefixes, size);
        ctxs_exts(musts[u].exts, size);
    }
}

static void
ctxs_when(const struct lysc_when *when, struct ly_ht *ht, int *size)
{
    uint32_t hash;

    /* ht check, make sure the structure is stored only once */
    hash = lyht_hash((const char *)&when, sizeof when);
    if (lyht_insert(ht, &when, hash, NULL) == LY_EEXIST) {
        return;
    }

    ctxs_expr(when->cond, size);
    ctxs_prefixes(when->prefixes, size);
    ctxs_exts(when->exts, size);
}

static void
ctxs_whens(const struct lysc_when **whens, struct ly_ht *ht, int *size)
{
    LY_ARRAY_COUNT_TYPE u;

    *size += sizeof(LY_ARRAY_COUNT_TYPE) + LY_ARRAY_COUNT(whens) * sizeof *whens;
    LY_ARRAY_FOR(whens, u) {
        ctxs_when(whens[u], ht, size);
    }
}

static void
ctxs_range(const struct lysc_range *range, int *size)
{
    if (!range) {
        return;
    }

    *size += sizeof *range;

    *size += sizeof(LY_ARRAY_COUNT_TYPE) + LY_ARRAY_COUNT(range->parts) * sizeof *range->parts;
    ctxs_exts(range->exts, size);
}

static void
ctxs_patterns(const struct lysc_pattern **patterns, struct ly_ht *ht, int *size)
{
    uint32_t hash;
    size_t code_size;
    LY_ARRAY_COUNT_TYPE u;

    *size += sizeof(LY_ARRAY_COUNT_TYPE) + LY_ARRAY_COUNT(patterns) * sizeof *patterns;
    LY_ARRAY_FOR(patterns, u) {
        /* ht check, make sure the structure is stored only once */
        hash = lyht_hash((const char *)patterns[u], sizeof *patterns);
        if (lyht_insert(ht, (void *)patterns[u], hash, NULL) == LY_EEXIST) {
            return;
        }

        pcre2_pattern_info(patterns[u]->code, PCRE2_INFO_SIZE, &code_size);
        *size += code_size;
        ctxs_exts(patterns[u]->exts, size);
    }
}

static void
ctxs_enums(const struct lysc_type_bitenum_item *enums, int *size)
{
    LY_ARRAY_COUNT_TYPE u;

    *size += sizeof(LY_ARRAY_COUNT_TYPE) + LY_ARRAY_COUNT(enums) * sizeof *enums;
    LY_ARRAY_FOR(enums, u) {
        ctxs_exts(enums[u].exts, size);
    }
}

static void
ctxs_type(const struct lysc_type *type, struct ly_ht *ht, int *size)
{
    uint32_t hash;
    const struct lysc_type_num *type_num;
    const struct lysc_type_dec *type_dec;
    const struct lysc_type_str *type_str;
    const struct lysc_type_enum *type_enum_bits;
    const struct lysc_type_leafref *type_lref;
    const struct lysc_type_identityref *type_identref;
    const struct lysc_type_instanceid *type_instid;
    const struct lysc_type_union *type_union;
    const struct lysc_type_bin *type_bin;
    LY_ARRAY_COUNT_TYPE u;

    /* ht check, make sure the structure is stored only once */
    hash = lyht_hash((const char *)&type, sizeof type);
    if (lyht_insert(ht, &type, hash, NULL) == LY_EEXIST) {
        return;
    }

    /* common members */
    ctxs_exts(type->exts, size);

    switch (type->basetype) {
    case LY_TYPE_BINARY:
        type_bin = (const struct lysc_type_bin *)type;
        *size += sizeof *type_bin;

        ctxs_range(type_bin->length, size);
        break;
    case LY_TYPE_UINT8:
    case LY_TYPE_UINT16:
    case LY_TYPE_UINT32:
    case LY_TYPE_UINT64:
    case LY_TYPE_INT8:
    case LY_TYPE_INT16:
    case LY_TYPE_INT32:
    case LY_TYPE_INT64:
        type_num = (const struct lysc_type_num *)type;
        *size += sizeof *type_num;

        ctxs_range(type_num->range, size);
        break;
    case LY_TYPE_STRING:
        type_str = (const struct lysc_type_str *)type;
        *size += sizeof *type_str;

        ctxs_range(type_str->length, size);
        ctxs_patterns((const struct lysc_pattern **)type_str->patterns, ht, size);
        break;
    case LY_TYPE_BITS:
    case LY_TYPE_ENUM:
        type_enum_bits = (const struct lysc_type_enum *)type;
        *size += sizeof *type_enum_bits;

        ctxs_enums(type_enum_bits->enums, size);
        break;
    case LY_TYPE_BOOL:
    case LY_TYPE_EMPTY:
        *size += sizeof *type;
        break;
    case LY_TYPE_DEC64:
        type_dec = (const struct lysc_type_dec *)type;
        *size += sizeof *type_dec;

        ctxs_range(type_dec->range, size);
        break;
    case LY_TYPE_IDENT:
        type_identref = (const struct lysc_type_identityref *)type;
        *size += sizeof *type_identref;

        *size += sizeof(LY_ARRAY_COUNT_TYPE) + LY_ARRAY_COUNT(type_identref->bases) * sizeof *type_identref->bases;
        break;
    case LY_TYPE_INST:
        type_instid = (const struct lysc_type_instanceid *)type;
        *size += sizeof *type_instid;
        break;
    case LY_TYPE_LEAFREF:
        type_lref = (const struct lysc_type_leafref *)type;
        *size += sizeof *type_lref;

        ctxs_expr(type_lref->path, size);
        ctxs_prefixes(type_lref->prefixes, size);
        break;
    case LY_TYPE_UNION:
        type_union = (const struct lysc_type_union *)type;
        *size += sizeof *type_union;

        *size += sizeof(LY_ARRAY_COUNT_TYPE) + LY_ARRAY_COUNT(type_union->types) * sizeof *type_union->types;
        LY_ARRAY_FOR(type_union->types, u) {
            ctxs_type(type_union->types[u], ht, size);
        }
        break;
    case LY_TYPE_UNKNOWN:
        LOGINT(NULL);
        break;
    }
}

static void
ctxs_node(const struct lysc_node *node, struct ly_ht *ht, int *size)
{
    const struct lysc_node_container *cont;
    const struct lysc_node_choice *choic;
    const struct lysc_node_leaf *leaf;
    const struct lysc_node_leaflist *llist;
    const struct lysc_node_list *list;
    const struct lysc_node_anydata *any;
    const struct lysc_node_case *cas;
    const struct lysc_node_action *act;
    const struct lysc_node_notif *notif;
    const struct lysc_node *child;
    LY_ARRAY_COUNT_TYPE u;

    /* common members */
    ctxs_exts(node->exts, size);

    switch (node->nodetype) {
    case LYS_CONTAINER:
        cont = (const struct lysc_node_container *)node;
        *size += sizeof *cont;

        LY_LIST_FOR(cont->child, child) {
            ctxs_node(child, ht, size);
        }
        ctxs_musts(cont->musts, size);
        ctxs_whens((const struct lysc_when **)cont->when, ht, size);
        LY_LIST_FOR((const struct lysc_node *)cont->actions, child) {
            ctxs_node(child, ht, size);
        }
        LY_LIST_FOR((const struct lysc_node *)cont->notifs, child) {
            ctxs_node(child, ht, size);
        }
        break;
    case LYS_CHOICE:
        choic = (const struct lysc_node_choice *)node;
        *size += sizeof *choic;

        LY_LIST_FOR((const struct lysc_node *)choic->cases, child) {
            ctxs_node(child, ht, size);
        }
        ctxs_whens((const struct lysc_when **)choic->when, ht, size);
        break;
    case LYS_LEAF:
        leaf = (const struct lysc_node_leaf *)node;
        *size += sizeof *leaf;

        ctxs_musts(leaf->musts, size);
        ctxs_whens((const struct lysc_when **)leaf->when, ht, size);
        ctxs_type(leaf->type, ht, size);
        ctxs_prefixes(leaf->dflt.prefixes, size);
        break;
    case LYS_LEAFLIST:
        llist = (const struct lysc_node_leaflist *)node;
        *size += sizeof *llist;

        ctxs_musts(llist->musts, size);
        ctxs_whens((const struct lysc_when **)llist->when, ht, size);
        ctxs_type(llist->type, ht, size);
        *size += sizeof(LY_ARRAY_COUNT_TYPE) + LY_ARRAY_COUNT(llist->dflts) * sizeof *llist->dflts;
        LY_ARRAY_FOR(llist->dflts, u) {
            ctxs_prefixes(llist->dflts[u].prefixes, size);
        }
        break;
    case LYS_LIST:
        list = (const struct lysc_node_list *)node;
        *size += sizeof *list;

        LY_LIST_FOR(list->child, child) {
            ctxs_node(child, ht, size);
        }
        ctxs_musts(list->musts, size);
        ctxs_whens((const struct lysc_when **)list->when, ht, size);
        LY_LIST_FOR((const struct lysc_node *)list->actions, child) {
            ctxs_node(child, ht, size);
        }
        LY_LIST_FOR((const struct lysc_node *)list->notifs, child) {
            ctxs_node(child, ht, size);
        }
        *size += sizeof(LY_ARRAY_COUNT_TYPE) + LY_ARRAY_COUNT(list->uniques) * sizeof *list->uniques;
        LY_ARRAY_FOR(list->uniques, u) {
            *size += sizeof(LY_ARRAY_COUNT_TYPE) + LY_ARRAY_COUNT(list->uniques[u]) * sizeof **list->uniques;
        }
        break;
    case LYS_ANYXML:
    case LYS_ANYDATA:
        any = (const struct lysc_node_anydata *)node;
        *size += sizeof *any;

        ctxs_musts(any->musts, size);
        ctxs_whens((const struct lysc_when **)any->when, ht, size);
        break;
    case LYS_CASE:
        cas = (const struct lysc_node_case *)node;
        *size += sizeof *cas;

        LY_LIST_FOR(cas->child, child) {
            ctxs_node(child, ht, size);
        }
        ctxs_whens((const struct lysc_when **)cas->when, ht, size);
        break;
    case LYS_RPC:
    case LYS_ACTION:
        act = (const struct lysc_node_action *)node;
        *size += sizeof *act;

        ctxs_whens((const struct lysc_when **)act->when, ht, size);
        LY_LIST_FOR(act->input.child, child) {
            ctxs_node(child, ht, size);
        }
        ctxs_musts(act->input.musts, size);
        LY_LIST_FOR(act->output.child, child) {
            ctxs_node(child, ht, size);
        }
        ctxs_musts(act->output.musts, size);
        break;
    case LYS_NOTIF:
        notif = (const struct lysc_node_notif *)node;
        *size += sizeof *notif;

        LY_LIST_FOR(notif->child, child) {
            ctxs_node(child, ht, size);
        }
        ctxs_musts(notif->musts, size);
        ctxs_whens((const struct lysc_when **)notif->when, ht, size);
        break;
    default:
        LOGINT(NULL);
        break;
    }
}

static void
ctxs_compiled(const struct lysc_module *compiled, struct ly_ht *ht, int *size)
{
    const struct lysc_node *node;

    if (!compiled) {
        return;
    }

    /* compiled module */
    *size += sizeof *compiled;

    *size += sizeof(LY_ARRAY_COUNT_TYPE) + LY_ARRAY_COUNT(compiled->features) * sizeof *compiled->features;
    LY_LIST_FOR(compiled->data, node) {
        ctxs_node(node, ht, size);
    }
    LY_LIST_FOR((const struct lysc_node *)compiled->rpcs, node) {
        ctxs_node(node, ht, size);
    }
    LY_LIST_FOR((const struct lysc_node *)compiled->notifs, node) {
        ctxs_node(node, ht, size);
    }
    ctxs_exts(compiled->exts, size);
}

static void
ctxs_module_extensions(const struct lysc_ext *extensions, int *size)
{
    LY_ARRAY_COUNT_TYPE u;

    /* sized array */
    *size += sizeof(LY_ARRAY_COUNT_TYPE) + LY_ARRAY_COUNT(extensions) * sizeof *extensions;

    LY_ARRAY_FOR(extensions, u) {
        ctxs_exts(extensions[u].exts, size);
    }
}

static void
ctxs_module_identities(const struct lysc_ident *identites, int *size)
{
    LY_ARRAY_COUNT_TYPE u;

    /* sized array */
    *size += sizeof(LY_ARRAY_COUNT_TYPE) + LY_ARRAY_COUNT(identites) * sizeof *identites;

    LY_ARRAY_FOR(identites, u) {
        *size += sizeof(LY_ARRAY_COUNT_TYPE) + LY_ARRAY_COUNT(identites[u].derived) * sizeof *identites[u].derived;
        ctxs_exts(identites[u].exts, size);
    }
}

static void
ctxs_module(const struct lys_module *mod, struct ly_ht *ht, int *size)
{
    /* module */
    *size += sizeof *mod;

    /* compiled module */
    ctxs_compiled(mod->compiled, ht, size);

    /* extensions, identities, submodules */
    ctxs_module_extensions(mod->extensions, size);
    ctxs_module_identities(mod->identities, size);
    *size += sizeof(LY_ARRAY_COUNT_TYPE) + LY_ARRAY_COUNT(mod->submodules) * sizeof *mod->submodules;

    /* augmented_by, deviated_by */
    *size += sizeof(LY_ARRAY_COUNT_TYPE) + LY_ARRAY_COUNT(mod->augmented_by) * sizeof *mod->augmented_by;
    *size += sizeof(LY_ARRAY_COUNT_TYPE) + LY_ARRAY_COUNT(mod->deviated_by) * sizeof *mod->deviated_by;
}

static ly_bool
ctxs_ptr_val_equal(void *val1_p, void *val2_p, ly_bool UNUSED(mod), void *UNUSED(cb_data))
{
    void *val1, *val2;

    val1 = *(void **)val1_p;
    val2 = *(void **)val2_p;

    return val1 == val2;
}

LIBYANG_API_DEF int
ly_ctx_print_compiled_size(const struct ly_ctx *ctx)
{
    int size = 0;
    uint32_t i;
    const struct lys_module *mod;
    struct ly_ht *ht;

    LY_CHECK_ARG_RET(NULL, ctx, -1);

    /* create hash table for shared structures */
    ht = lyht_new(0, sizeof(void *), ctxs_ptr_val_equal, NULL, 1);
    LY_CHECK_RET(!ht, -1);

    /* dictionary (with all the strings) */
    ctxs_dict_ht(ctx->dict.hash_tab, &size);

    /* module count */
    size += sizeof ctx->list.count;
    for (i = 0; i < ctx->list.count; ++i) {
        mod = ctx->list.objs[i];

        /* modules */
        ctxs_module(mod, ht, &size);
    }

    lyht_free(ht, NULL);
    return size;
}

static void
ctxs_identity(const struct lysc_ident *ident, int *size)
{
    *size += sizeof *ident;
    ctxs_exts(ident->exts, size);
}

int
ly_ctx_print_compiled_ext_stmt_size(const struct lysc_ext_substmt *substmts)
{
    LY_ARRAY_COUNT_TYPE u;
    struct ly_ht *ht;
    int size = 0;
    uint32_t hash;
    const struct lysc_node *node;

    /* create hash table for shared structures */
    ht = lyht_new(0, sizeof(void *), ctxs_ptr_val_equal, NULL, 1);
    LY_CHECK_RET(!ht, -1);

    size += sizeof(LY_ARRAY_COUNT_TYPE) + LY_ARRAY_COUNT(substmts) * sizeof *substmts;
    LY_ARRAY_FOR(substmts, u) {
        switch (substmts[u].stmt) {
        case LY_STMT_NOTIFICATION:
        case LY_STMT_INPUT:
        case LY_STMT_OUTPUT:
        case LY_STMT_ACTION:
        case LY_STMT_RPC:
        case LY_STMT_ANYDATA:
        case LY_STMT_ANYXML:
        case LY_STMT_CASE:
        case LY_STMT_CHOICE:
        case LY_STMT_CONTAINER:
        case LY_STMT_LEAF:
        case LY_STMT_LEAF_LIST:
        case LY_STMT_LIST:
        case LY_STMT_USES:
            node = *(const struct lysc_node **)substmts[u].storage_p;

            /* ht check, make sure the node list is stored only once */
            hash = lyht_hash((const char *)&node, sizeof node);
            if (lyht_insert(ht, &node, hash, NULL) == LY_EEXIST) {
                break;
            }

            size += sizeof node;
            LY_LIST_FOR(node, node) {
                ctxs_node(node, ht, &size);
            }
            break;
        case LY_STMT_ARGUMENT:
        case LY_STMT_CONTACT:
        case LY_STMT_DESCRIPTION:
        case LY_STMT_ERROR_APP_TAG:
        case LY_STMT_ERROR_MESSAGE:
        case LY_STMT_KEY:
        case LY_STMT_MODIFIER:
        case LY_STMT_NAMESPACE:
        case LY_STMT_ORGANIZATION:
        case LY_STMT_PRESENCE:
        case LY_STMT_REFERENCE:
        case LY_STMT_UNITS:
            /* string, in the dictionary */
            size += sizeof(char *);
            break;
        case LY_STMT_BIT:
        case LY_STMT_ENUM:
            size += sizeof(struct lysc_type_bitenum_item *);
            ctxs_enums(*substmts[u].storage_p, &size);
            break;
        case LY_STMT_CONFIG:
        case LY_STMT_MANDATORY:
        case LY_STMT_ORDERED_BY:
        case LY_STMT_STATUS:
            size += sizeof(uint16_t);
            break;
        case LY_STMT_EXTENSION_INSTANCE:
            size += sizeof(struct lysc_ext_instance *);
            ctxs_exts(*substmts[u].storage_p, &size);
            break;
        case LY_STMT_FRACTION_DIGITS:
        case LY_STMT_REQUIRE_INSTANCE:
            size += sizeof(uint8_t);
            break;
        case LY_STMT_IDENTITY:
            size += sizeof(struct lysc_ident *);
            ctxs_identity(*substmts[u].storage_p, &size);
            break;
        case LY_STMT_LENGTH:
        case LY_STMT_RANGE:
            size += sizeof(struct lysc_range *);
            ctxs_range(*substmts[u].storage_p, &size);
            break;
        case LY_STMT_MAX_ELEMENTS:
        case LY_STMT_MIN_ELEMENTS:
            size += sizeof(uint32_t);
            break;
        case LY_STMT_MUST:
            size += sizeof(struct lysc_must *);
            ctxs_musts(*substmts[u].storage_p, &size);
            break;
        case LY_STMT_PATTERN:
            size += sizeof(struct lysc_pattern **);
            ctxs_patterns(*substmts[u].storage_p, ht, &size);
            break;
        case LY_STMT_POSITION:
        case LY_STMT_VALUE:
            size += sizeof(uint64_t);
            break;
        case LY_STMT_TYPE:
            size += sizeof(struct lysc_type *);
            ctxs_type(*substmts[u].storage_p, ht, &size);
            break;
        case LY_STMT_WHEN:
            size += sizeof(struct lysc_when *);
            ctxs_when(*substmts[u].storage_p, ht, &size);
            break;
        case LY_STMT_NONE:
        case LY_STMT_AUGMENT:
        case LY_STMT_GROUPING:
        case LY_STMT_BASE:
        case LY_STMT_BELONGS_TO:
        case LY_STMT_DEFAULT:
        case LY_STMT_DEVIATE:
        case LY_STMT_DEVIATION:
        case LY_STMT_EXTENSION:
        case LY_STMT_FEATURE:
        case LY_STMT_IF_FEATURE:
        case LY_STMT_IMPORT:
        case LY_STMT_INCLUDE:
        case LY_STMT_MODULE:
        case LY_STMT_PATH:
        case LY_STMT_PREFIX:
        case LY_STMT_REFINE:
        case LY_STMT_REVISION:
        case LY_STMT_REVISION_DATE:
        case LY_STMT_SUBMODULE:
        case LY_STMT_TYPEDEF:
        case LY_STMT_UNIQUE:
        case LY_STMT_YANG_VERSION:
        case LY_STMT_YIN_ELEMENT:
        case LY_STMT_SYNTAX_SEMICOLON:
        case LY_STMT_SYNTAX_LEFT_BRACE:
        case LY_STMT_SYNTAX_RIGHT_BRACE:
        case LY_STMT_ARG_TEXT:
        case LY_STMT_ARG_VALUE:
            /* not compiled, unreachable */
            LOGINT(NULL);
            size = -1;
            goto cleanup;
        }
    }

cleanup:
    lyht_free(ht, NULL);
    return size;
}

LIBYANG_API_DEF LY_ERR
ly_ctx_print_compiled(const struct ly_ctx *orig_ctx, void *mem, struct ly_ctx **ctx)
{

}
