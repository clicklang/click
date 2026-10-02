# A variadic prototype is retained as a declaration

A body-less prototype ending in `, ...` declares an external function. It
contributes no executable code and no proof facts, so a translation unit
that only declares it verifies exactly as it would without the declaration.
The header and source below repeat the declaration compatibly, with and
without `extern`, and with an allowlisted function attribute.

```c filename=include/report.h
extern int report(const char *format, ...);
void halt(const char *format, ...) __attribute__((__noreturn__));
```

```c filename=c_variadic_prototype_declared.c
#include "include/report.h"

int report(const char *format,
           ...);

int32 keep(int32 value) {
    return value;
}
```

```click
verifying "c_variadic_prototype_declared.c";

int32 keep(int32 value) {
    ensures result == value by auto;
}
```

```expect
pass
```
