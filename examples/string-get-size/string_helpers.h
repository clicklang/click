/* SPDX-License-Identifier: GPL-2.0-only */
#ifndef STRING_HELPERS_H
#define STRING_HELPERS_H
/* Hand-written stand-in for the kernel headers string_get_size uses. */
typedef unsigned int u32;
typedef unsigned long u64;
typedef unsigned int uint32_t;
typedef unsigned long uint64_t;
#define BIT(nr) (1UL << (nr))
#define ARRAY_SIZE(arr) (sizeof(arr) / sizeof((arr)[0]))
enum string_size_units {
	STRING_UNITS_10,
	STRING_UNITS_2,
	STRING_UNITS_MASK	= BIT(0),
	STRING_UNITS_NO_SPACE	= BIT(30),
	STRING_UNITS_NO_BYTES	= BIT(31),
};
/* include/asm-generic/div64.h, BITS_PER_LONG == 64 */
# define do_div(n,base) ({					\
	uint32_t __base = (base);				\
	uint32_t __rem;						\
	__rem = ((uint64_t)(n)) % __base;			\
	(n) = ((uint64_t)(n)) / __base;				\
	__rem;							\
 })
int snprintf(char *buf, unsigned long size, const char *fmt, ...);
#endif
