# A caller's C-string requirement reaches `strlen` in a `return` and through a copy

Equivalent C forms verify alike. A caller that requires `cstr_readable`
discharges `strlen`'s precondition when the call is the returned expression,
and when the pointer reaches the call through a local copy with no store in
between.

```c filename=cstr_return_and_copy.c
#include <string.h>

size_t returned(const char *s) {
    return strlen(s);
}

uint64 copied(uint8 bytes[]) {
    uint8* p;
    p = bytes;
    return strlen(p);
}
```

```click
target "x86_64-linux-userspace";
verifying "cstr_return_and_copy.c";

uint64 returned(const char* s) {
    requires cstr_readable(s);
    ensures s[result] == '\0';
} by {
    execute();
    simp();
}

uint64 copied(uint8 bytes[]) {
    requires cstr_readable(bytes);
    ensures bytes[result] == '\0';
} by {
    execute();
    simp();
}
```

```expect
pass
```
