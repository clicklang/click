# Built-in `<string.h>` and `<stdlib.h>` reach the library contracts

Click supplies its own declaration-only `<string.h>` and `<stdlib.h>` for the
user-space target. They declare exactly the functions Click specifies, so a
program that includes them, rather than declaring the prototypes by hand,
verifies against the same `memcpy` contract and allocation model with no
compiler import. `NULL` comes from either header.

```c filename=builtin_libc_headers.c
#include <stdlib.h>
#include <string.h>

struct pair {
    int a;
    int b;
};

int copy_pair(void) {
    struct pair *src = malloc(sizeof(struct pair));
    if (src == NULL) {
        return -1;
    }
    struct pair *dst = malloc(sizeof(struct pair));
    if (dst == NULL) {
        free(src);
        return -1;
    }
    src->a = 3;
    src->b = 4;
    memcpy((unsigned char *)(void *)dst, (unsigned char *)(void *)src,
           sizeof(struct pair));
    int out = dst->a + dst->b;
    free(src);
    free(dst);
    return out;
}
```

```click
target "x86_64-linux-userspace";
verifying "builtin_libc_headers.c";

int copy_pair() {
    ensures result == 7 or result == -1;
} by {
    execute();
    simp();
}
```

```expect
pass
```
