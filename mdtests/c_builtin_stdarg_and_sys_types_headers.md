# Built-in `<stdarg.h>` and `<sys/types.h>` supply their types

Click's user-space `<stdarg.h>` declares only `va_list`, so a prototype that
takes one parses, as zlib's `zconf.h` and `zlib.h` need. Its `<sys/types.h>`
declares `ssize_t` and `off_t`, both `long` on LP64. Neither header adds
executable code. The access macros `va_start`, `va_arg`, `va_copy` and
`va_end` are not provided: a variadic definition is refused on its own (see
`mdtests/c_variadic_prototype_declared.md`).

```c filename=types_headers.c
#include <stdarg.h>
#include <sys/types.h>

int format_list(const char *format, va_list args);

off_t advance(off_t offset, ssize_t step) {
    return offset + step;
}
```

```click
target "x86_64-linux-userspace";
verifying "types_headers.c";

int64 advance(int64 offset, int64 step) {
    requires offset + step <= 9223372036854775807;
    requires offset + step >= -9223372036854775807 - 1;
    ensures result == offset + step;
} by {
    execute();
    simp();
}
```

```expect
pass
```
