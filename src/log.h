/**
 * @file log.h
 * @author Radek Krejci <rkrejci@cesnet.cz>
 * @author Michal Vasko <mvasko@cesnet.cz>
 * @brief Logger manipulation routines and error definitions.
 *
 * Copyright (c) 2015 - 2022 CESNET, z.s.p.o.
 *
 * This source code is licensed under BSD 3-Clause License (the "License").
 * You may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     https://opensource.org/licenses/BSD-3-Clause
 */

#ifndef LY_LOG_H_
#define LY_LOG_H_

#include <stdint.h>

#include "config.h"

#ifdef __cplusplus
extern "C" {
#endif

/* dummy context structure */
struct ly_ctx;

/**
 * @brief Type to indicate boolean value.
 *
 * Do not test for actual value. Instead, handle it as true/false value in condition.
 */
typedef uint8_t ly_bool;

/**
 * @page howtoLogger Information Logging
 *
 * The libyang logger is supposed to process all the messages (and some other accompanied information) generated by the performed
 * functions. According to the logger settings, the information can be printed, stored or further processed by a callback
 * functions.
 *
 * The logger is tightly connected with [errors handling](@ref howtoErrors), because when an error appears, the logger (according
 * to [logger options](@ref logopts)) generates error records available via libyang context.
 *
 * There are 4 verbosity levels defined as ::LY_LOG_LEVEL. The level can be changed by the ::ly_log_level() function.
 * By default, the verbosity level is set to #LY_LLERR value, so only the errors are processed.
 *
 * By default, all libyang messages are printed to `stderr`. However, the callers are able to set their own logging callback
 * function (::ly_log_clb). In that case, instead of printing messages, libyang passes error level, message and path (if any) to
 * the caller's callback function set via ::ly_set_log_clb(). In case of error level, the error information is still
 * automatically stored and available via the [error handling functions](@ref howtoErrors).
 *
 * With [logging options](@ref logopts) set via ::ly_log_options(), the caller can modify what is done with all the messages.
 * Default flags are ::LY_LOLOG and ::LY_LOSTORE_LAST so that messages are logged and the last one is stored. If you set the flag
 * ::LY_LOSTORE, all the messages will be stored. Be careful because unless you regularly clean them, the error list in context
 * will grow indefinitely.
 *
 * As a separate group, there are @ref dbggroup to select group of debugging messages to print. The options can be set via
 * ::ly_log_dbg_groups() function, but note that the options take effect only in case the libyang is compiled in
 * [Debug build mode](@ref build).
 *
 * \note API for this group of functions is described in the [logger module](@ref log).
 *
 * Functions List
 * --------------
 * - ::ly_log_level()
 * - ::ly_log_dbg_groups()
 * - ::ly_log_options()
 * - ::ly_set_log_clb()
 * - ::ly_get_log_clb()
 *
 */

/**
 * @defgroup log Logger
 * @{
 *
 * Publicly visible functions and values of the libyang logger. For more
 * information, see @ref howtoLogger.
 */

/**
 * @typedef LY_LOG_LEVEL
 * @brief Verbosity levels of the libyang logger.
 */
typedef enum {
    LY_LLERR = 0, /**< Print only error messages. */
    LY_LLWRN = 1, /**< Print error and warning messages, default value. */
    LY_LLVRB = 2, /**< Besides errors and warnings, print some other verbose messages. */
    LY_LLDBG = 3  /**< Print all messages including some development debug messages (be careful,
                       without subsequently calling ::ly_log_dbg_groups() no debug messages will be printed!). */
} LY_LOG_LEVEL;

/**
 * @brief Set logger verbosity level.
 *
 * To get the current value, the function must be called twice resetting the level by the received value.
 *
 * @param[in] level Verbosity level.
 * @return Previous verbosity level.
 */
LIBYANG_API_DECL LY_LOG_LEVEL ly_log_level(LY_LOG_LEVEL level);

/**
 * @ingroup logger
 * @defgroup logopts Logging options
 *
 * Logging option bits of libyang.
 *
 * Can be set via ::ly_log_options().
 *
 * @{
 */
#define LY_LOLOG        0x01 /**< Log messages normally, using callback if set. If not set, messages will
                                  not be printed by libyang. */
#define LY_LOSTORE      0x02 /**< Store any generated errors or warnings, never verbose or debug messages.
                                  Note that if #LY_LOLOG is not set then verbose and debug messages are always lost. */
#define LY_LOSTORE_LAST 0x06 /**< Store any generated errors or warnings but only the last message, always overwrite
                                  the previous one. */

/**
 * @}
 */

/**
 * @brief Set logger options. Default is #LY_LOLOG | #LY_LOSTORE_LAST.
 *
 * To get the current value, the function must be called twice resetting the level by the received value.
 *
 * @param[in] opts Bitfield of @ref logopts.
 * @return Previous logger options.
 */
LIBYANG_API_DECL uint32_t ly_log_options(uint32_t opts);

/**
 * @brief Set temporary thread-safe logger options overwriting those set by ::ly_log_options().
 *
 * @param[in] opts Pointer to the temporary @ref logopts. If NULL, restores the effect of global logger options.
 */
LIBYANG_API_DECL void ly_temp_log_options(uint32_t *opts);

#ifndef NDEBUG

/**
 * @ingroup log
 * @defgroup dbggroup Debug messages groups
 *
 * Categories of the debug messages.
 *
 * Allows to show only the selected group(s) of the debug messages.
 *
 * @{
 */

#define LY_LDGDICT      0x01    /**< Dictionary additions and deletions. */
#define LY_LDGXPATH     0x02    /**< XPath parsing end evaluation. */
#define LY_LDGDEPSETS   0x04    /**< Dependency module sets for schema compilation. */

/**
 * @}
 */

/**
 * @brief Enable specific debugging messages (independent of log level).
 *
 * To get the current value, the function must be called twice resetting the level by the received value.
 *
 * @param[in] dbg_groups Bitfield of enabled debug message groups (see @ref dbggroup).
 * @return Previous options bitfield.
 */
uint32_t ly_log_dbg_groups(uint32_t dbg_groups);

#endif

/**
 * @brief Logger callback.
 *
 * !IMPORTANT! If an error has a specific error-app-tag defined in the model, it will NOT be set
 *             at the time of calling this callback. It will be set right after, so to retrieve it
 *             it must be checked afterwards with ::ly_errapptag().
 *
 * @param[in] level Log level of the message.
 * @param[in] msg Message.
 * @param[in] path Optional path of the concerned node.
 */
typedef void (*ly_log_clb)(LY_LOG_LEVEL level, const char *msg, const char *path);

/**
 * @brief Set logger callback.
 *
 * @param[in] clb Logging callback.
 * @param[in] path flag to resolve and provide path as the third parameter of the callback function. In case of
 *            validation and some other errors, it can be useful to get the path to the problematic element. Note,
 *            that according to the tree type and the specific situation, the path can slightly differs (keys
 *            presence) or it can be NULL, so consider it as an optional parameter. If the flag is 0, libyang will
 *            not bother with resolving the path.
 */
LIBYANG_API_DECL void ly_set_log_clb(ly_log_clb clb, ly_bool path);

/**
 * @brief Get logger callback.
 * @return Logger callback (can be NULL).
 */
LIBYANG_API_DECL ly_log_clb ly_get_log_clb(void);

/** @} log */

/**
 * @page howtoErrors Errors Handling
 *
 * The most of the API functions directly returns error code in the form of ::LY_ERR value. In addition, if the ::LY_EVALID error
 * arises, additional [validation error code](@ref ::LY_VECODE) is provided to categorize validation failures into several groups.
 *
 * All the errors arisen in connection with manipulation with the [context](@ref howtoContext), [YANG modules](@ref howtoSchema)
 * or [YANG data](@ref howtoData), are recorded into the context and can be examined for the more detailed information. These
 * records are stored as ::ly_err_item structures and they are not only context-specific, but also thread-specific.
 *
 * Storing error information is tightly connected with
 * [logging](@ref howtoLogger). So the @ref logopts control if and which errors are stored in the context. By default, only the
 * last error is recorded, so a new error replaces the previous one. This can be changed with ::LY_LOSTORE option set via
 * ::ly_log_options(). Then, the errors are stored as a list preserving the previous error records. The stored records can be
 * accessed using ::ly_err_last() or ::ly_err_first() functions. The ::ly_err_clean() is used to remove error records from the
 * context.
 *
 * To print a specific error information via libyang logger, there is ::ly_err_print().
 *
 * To simplify access to the last error record in the context, there is a set of functions returning important error information.
 * - ::ly_errapptag()
 * - ::ly_errcode()
 * - ::ly_vecode()
 * - ::ly_errmsg()
 * - ::ly_errpath()
 *
 * \note API for this group of functions is described in the [error information module](@ref errors).
 */

/**
 * @defgroup errors Error information
 *
 * Structures and functions to allow error information processing.
 *
 * @{
 */

/**
 * @typedef LY_ERR
 * @brief libyang's error codes returned by the libyang functions.
 */
typedef enum {
    LY_SUCCESS = 0, /**< no error, not set by functions, included just to complete #LY_ERR enumeration */
    LY_EMEM,        /**< Memory allocation failure */
    LY_ESYS,        /**< System call failure */
    LY_EINVAL,      /**< Invalid value */
    LY_EEXIST,      /**< Item already exists */
    LY_ENOTFOUND,   /**< Item does not exists */
    LY_EINT,        /**< Internal error */
    LY_EVALID,      /**< Validation failure */
    LY_EDENIED,     /**< Operation is not allowed */
    LY_EINCOMPLETE, /**< The operation did not fail, but for some reason it was not possible to finish it completely.
                         According to the specific use case, the caller is usually supposed to perform the operation again. */
    LY_ERECOMPILE,  /**< The operation did not fail, but requires context recompilation before it can be completed.
                         According to the specific use case, the caller should react appropriately. */
    LY_ENOT,        /**< Negative result */
    LY_EOTHER,      /**< Unknown error */

    LY_EPLUGIN = 128/**< Error reported by a plugin - the highest bit in the first byte is set.
                         This value is used ORed with one of the other LY_ERR value and can be simply masked. */
} LY_ERR;

/**
 * @ingroup logger
 * @typedef LY_VECODE
 * @brief libyang's codes of validation error. Whenever ly_errno is set to LY_EVALID, the ly_vecode is also set
 * to the appropriate LY_VECODE value.
 */
typedef enum {
    LYVE_SUCCESS = 0,  /**< no error */
    LYVE_SYNTAX,       /**< generic syntax error */
    LYVE_SYNTAX_YANG,  /**< YANG-related syntax error */
    LYVE_SYNTAX_YIN,   /**< YIN-related syntax error */
    LYVE_REFERENCE,    /**< invalid referencing or using an item */
    LYVE_XPATH,        /**< invalid XPath expression */
    LYVE_SEMANTICS,    /**< generic semantic error */
    LYVE_SYNTAX_XML,   /**< XML-related syntax error */
    LYVE_SYNTAX_JSON,  /**< JSON-related syntax error */
    LYVE_DATA,         /**< YANG data does not reflect some of the module restrictions */

    LYVE_OTHER         /**< Unknown error */
} LY_VECODE;

/**
 * @brief Libyang full error structure.
 */
struct ly_err_item {
    LY_LOG_LEVEL level;
    LY_ERR no;
    LY_VECODE vecode;
    char *msg;
    char *path;
    char *apptag;
    struct ly_err_item *next;
    struct ly_err_item *prev; /* first item's prev points to the last item */
};

/**
 * @brief Get the last (thread-specific) error message.
 *
 * ::ly_errmsg() should be used instead of this function but this one is useful for getting
 * errors from functions that do not have any context accessible. Or as a simple unified logging API.
 *
 * @return Last generated error message.
 */
LIBYANG_API_DECL const char *ly_last_errmsg(void);

/**
 * @brief Get the last (thread, context-specific) validation error code.
 *
 * This value is set only if ly_errno is #LY_EVALID.
 *
 * @param[in] ctx Relative context.
 * @return Validation error code.
 */
LIBYANG_API_DECL LY_VECODE ly_vecode(const struct ly_ctx *ctx);

/**
 * @brief Get the last (thread, context-specific) error code.
 *
 * @param[in] ctx Relative context.
 * @return LY_ERR value of the last error code.
 */
LIBYANG_API_DECL LY_ERR ly_errcode(const struct ly_ctx *ctx);

/**
 * @brief Get the last (thread, context-specific) error message. If the coresponding module defined
 * a specific error message, it will be used instead the default one.
 *
 * Sometimes, the error message is extended with path of the element where the problem is.
 * The path is available via ::ly_errpath().
 *
 * @param[in] ctx Relative context.
 * @return Text of the last error message, empty string if there is no error.
 */
LIBYANG_API_DECL const char *ly_errmsg(const struct ly_ctx *ctx);

/**
 * @brief Get the last (thread, context-specific) path of the element where was an error.
 *
 * The path always corresponds to the error message available via ::ly_errmsg(), so
 * whenever a subsequent error message is printed, the path is erased or rewritten.
 * The path reflects the type of the processed tree - data path for data tree functions
 * and schema path in case of schema tree functions. In case of processing YIN schema
 * or XML data, the path can be just XML path. In such a case, the corresponding
 * ly_vecode (value 1-3) is set.
 *
 * @param[in] ctx Relative context.
 * @return Path of the error element, empty string if error path does not apply to the last error.
 */
LIBYANG_API_DECL const char *ly_errpath(const struct ly_ctx *ctx);

/**
 * @brief Get the last (thread, context-specific) error-app-tag if there was a specific one defined
 * in the module for the last error.
 *
 * The app-tag always corresponds to the error message available via ::ly_errmsg(), so
 * whenever a subsequent error message is printed, the app-tag is erased or rewritten.
 *
 * @param[in] ctx Relative context.
 * @return Error-app-tag of the last error, empty string if the error-app-tag does not apply to the last error.
 */
LIBYANG_API_DECL const char *ly_errapptag(const struct ly_ctx *ctx);

/**
 * @brief Get the first (thread, context-specific) generated error structure.
 *
 * @param[in] ctx Relative context.
 * @return The first error structure (can be NULL), do not modify!
 */
LIBYANG_API_DECL struct ly_err_item *ly_err_first(const struct ly_ctx *ctx);

/**
 * @brief Get the latest (thread, context-specific) generated error structure.
 *
 * @param[in] ctx Relative context.
 * @return The last error structure (can be NULL), do not modify!
 */
LIBYANG_API_DECL struct ly_err_item *ly_err_last(const struct ly_ctx *ctx);

/**
 * @brief Print the error structure as if just generated.
 *
 * @param[in] ctx Optional context to store the message in.
 * @param[in] eitem Error item structure to print.
 */
LIBYANG_API_DECL void ly_err_print(const struct ly_ctx *ctx, struct ly_err_item *eitem);

/**
 * @brief Free error structures from a context.
 *
 * If \p eitem is not set, free all the error structures.
 *
 * @param[in] ctx Relative context.
 * @param[in] eitem Oldest error structure to remove, optional.
 */
LIBYANG_API_DECL void ly_err_clean(struct ly_ctx *ctx, struct ly_err_item *eitem);

/** @} errors */

#ifdef __cplusplus
}
#endif

#endif /* LY_LOG_H_ */
