# Linux `string_get_size`

`string_get_size.c` is a C transcription of `string_get_size` from Linux
`lib/string_helpers.c` at tag `v7.3`:

<https://github.com/torvalds/linux/blob/v7.3/lib/string_helpers.c>

The function, including its comment, is copied byte-for-byte. The
translations are:

- The upstream file's includes are replaced by `#include "string_helpers.h"`,
  a local stand-in that declares only what the function uses: the `u32` and
  `u64` typedefs, `BIT` and `ARRAY_SIZE`, `enum string_size_units` (from
  `include/linux/string_helpers.h`), `do_div` as the 64-bit
  `include/asm-generic/div64.h` defines it, and `snprintf`.
- The rest of `lib/string_helpers.c` and `EXPORT_SYMBOL(string_get_size)` are
  left out.

The source is GPL-2.0-only, as the upstream file is.
