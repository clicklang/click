# The built-in `<string.h>` declares the standard `strlen`

Click's `<string.h>` declares `size_t strlen(const char *s)`, and a call
binds to the standard-library contract: the caller's `cstr_readable`
requirement, stated over its `const char *` parameter, discharges the
contract's precondition. Plain `char` is unsigned 8-bit on every supported
target, so a C string and `uint8` bytes are the same values in a
specification.

```c filename=builtin_strlen.c
#include <string.h>

int last_index(const char *s) {
    int n = strlen(s);
    return n;
}
```

```click
target "x86_64-linux-userspace";
verifying "builtin_strlen.c";

int32 last_index(const char* s) {
    requires cstr_readable(s);
    ensures s[result] == '\0';
} by {
    execute();
    simp();
}
```

```expect
pass
```
