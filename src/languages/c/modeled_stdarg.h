/* Click's <stdarg.h>: the `va_list` type, so prototypes that take one parse.
 * Click does not model variadic function bodies, so the access macros
 * `va_start`, `va_arg`, `va_copy` and `va_end` are not provided. */
#pragma once
typedef __builtin_va_list va_list;
