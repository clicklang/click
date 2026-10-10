# A different definition of a `<limits.h>` name conflicts

A program's own `INT_MAX` with a different value is a conflicting
redefinition when the built-in `<limits.h>` is included, as under a C
compiler.

```c filename=limits_conflict.c
#define INT_MAX 7
#include <limits.h>

int f(void) {
    return INT_MAX;
}
```

```click
verifying "limits_conflict.c";

int f() {
    ensures result == 7;
} by {
    execute();
    simp();
}
```

```expect
fail: macro `INT_MAX` is redefined by <limits.h>
```
