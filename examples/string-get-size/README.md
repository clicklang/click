# Linux `string_get_size`

`string_get_size` formats a size, `size` blocks of `blk_size` bytes, to three
significant figures with a unit (`kB`, `MiB`, ...) into `buf`. The proof covers
the unchanged function for both unit systems, powers of 1000 and of 1024, and
every combination of `STRING_UNITS_NO_SPACE` and `STRING_UNITS_NO_BYTES`. For
any `size`, `blk_size`, and `units` and a buffer of at least 9 bytes it proves:

- the function has no undefined behavior;
- the result, the number of characters the format produces, is not negative;
- `buf` holds a terminated string: the terminator follows the output when it
  fits and is the buffer's last byte when it does not.

The proof is organized around the function's joins. Each reduction loop
divides by `divisor[units_base]` once per iteration, read through a proof `if`
join that keeps only `1000 <= divisor <= 1024`, and its bounds are stated in
Integer form, so one proof covers both divisors. The binary remainder
conversion, the rounding read `rounding[j]`, the carry, and the `.%03u`
fraction string `tmp` each rejoin through a `branch` or proof `if` interface;
`tmp` is exported as a C string of length `tmp_len(j)`. Only the final
`snprintf`, which prints a different literal for each unit and flag, splits
into its 76 cases.

It verifies in about a minute, so it runs in the nightly example suite.
Run `click verify string_get_size.click` in this directory. See `SOURCE.md`
for the source and its translations.
