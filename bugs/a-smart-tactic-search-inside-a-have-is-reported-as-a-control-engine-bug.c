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
int s3(u64 size, u32 remainder, const enum string_size_units units,
       char *buf, int len)
{
	enum string_size_units units_base = units & STRING_UNITS_MASK;
	static const unsigned int rounding[] = { 500, 50, 5 };
	int j;
	u32 sf_cap;
	char tmp[12];

	tmp[0] = '\0';

	sf_cap = size;
	for (j = 0; sf_cap*10 < 1000; j++)
		sf_cap *= 10;

	if (units_base == STRING_UNITS_2) {
		remainder *= 1000;
		remainder >>= 10;
	}

	remainder += rounding[j];
	if (remainder >= 1000) {
		remainder -= 1000;
		size += 1;
	}

	if (j) {
		snprintf(tmp, sizeof(tmp), ".%03u", remainder);
		tmp[j+1] = '\0';
	}

	return snprintf(buf, len, "%u%s", (u32)size, tmp);
}
