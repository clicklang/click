// SPDX-License-Identifier: GPL-2.0-only
#include "string_helpers.h"

/**
 * string_get_size - get the size in the specified units
 * @size:	The size to be converted in blocks
 * @blk_size:	Size of the block (use 1 for size in bytes)
 * @units:	Units to use (powers of 1000 or 1024), whether to include space separator
 * @buf:	buffer to format to
 * @len:	length of buffer
 *
 * This function returns a string formatted to 3 significant figures
 * giving the size in the required units.  @buf should have room for
 * at least 9 bytes and will always be zero terminated.
 *
 * Return value: number of characters of output that would have been written
 * (which may be greater than len, if output was truncated).
 */
int string_get_size(u64 size, u64 blk_size, const enum string_size_units units,
		    char *buf, int len)
{
	enum string_size_units units_base = units & STRING_UNITS_MASK;
	static const char *const units_10[] = {
		"", "k", "M", "G", "T", "P", "E", "Z", "Y",
	};
	static const char *const units_2[] = {
		"", "Ki", "Mi", "Gi", "Ti", "Pi", "Ei", "Zi", "Yi",
	};
	static const char *const *const units_str[] = {
		[STRING_UNITS_10] = units_10,
		[STRING_UNITS_2] = units_2,
	};
	static const unsigned int divisor[] = {
		[STRING_UNITS_10] = 1000,
		[STRING_UNITS_2] = 1024,
	};
	static const unsigned int rounding[] = { 500, 50, 5 };
	int i = 0, j;
	u32 remainder = 0, sf_cap;
	char tmp[12];
	const char *unit;

	tmp[0] = '\0';

	if (blk_size == 0)
		size = 0;
	if (size == 0)
		goto out;

	/* This is Napier's algorithm.  Reduce the original block size to
	 *
	 * coefficient * divisor[units_base]^i
	 *
	 * we do the reduction so both coefficients are just under 32 bits so
	 * that multiplying them together won't overflow 64 bits and we keep
	 * as much precision as possible in the numbers.
	 *
	 * Note: it's safe to throw away the remainders here because all the
	 * precision is in the coefficients.
	 */
	while (blk_size >> 32) {
		do_div(blk_size, divisor[units_base]);
		i++;
	}

	while (size >> 32) {
		do_div(size, divisor[units_base]);
		i++;
	}

	/* now perform the actual multiplication keeping i as the sum of the
	 * two logarithms */
	size *= blk_size;

	/* and logarithmically reduce it until it's just under the divisor */
	while (size >= divisor[units_base]) {
		remainder = do_div(size, divisor[units_base]);
		i++;
	}

	/* work out in j how many digits of precision we need from the
	 * remainder */
	sf_cap = size;
	for (j = 0; sf_cap*10 < 1000; j++)
		sf_cap *= 10;

	if (units_base == STRING_UNITS_2) {
		/* express the remainder as a decimal.  It's currently the
		 * numerator of a fraction whose denominator is
		 * divisor[units_base], which is 1 << 10 for STRING_UNITS_2 */
		remainder *= 1000;
		remainder >>= 10;
	}

	/* add a 5 to the digit below what will be printed to ensure
	 * an arithmetical round up and carry it through to size */
	remainder += rounding[j];
	if (remainder >= 1000) {
		remainder -= 1000;
		size += 1;
	}

	if (j) {
		snprintf(tmp, sizeof(tmp), ".%03u", remainder);
		tmp[j+1] = '\0';
	}

 out:
	if (i >= ARRAY_SIZE(units_2))
		unit = "UNK";
	else
		unit = units_str[units_base][i];

	return snprintf(buf, len, "%u%s%s%s%s", (u32)size, tmp,
			(units & STRING_UNITS_NO_SPACE) ? "" : " ",
			unit,
			(units & STRING_UNITS_NO_BYTES) ? "" : "B");
}
