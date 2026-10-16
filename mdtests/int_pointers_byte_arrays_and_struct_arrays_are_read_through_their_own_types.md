# `int *` cells, byte arrays and struct arrays read through their own types

The strict-aliasing check allows each of these accesses:

- an `int *` read through an `int **` parameter;
- a declared `int *` read through an `int **`;
- a member of a local struct array;
- a byte of a local `uint8_t` array read through an `unsigned char *`.

```c filename=own.c
#include <stdint.h>
struct pair { int a; long b; };

int ptrs_own(int **a) {
    return *a == 0;
}

int local_cell(void) {
    int x = 3;
    int *p = &x;
    int **q = &p;
    return **q;
}

long struct_array(void) {
    struct pair items[2];
    items[1].a = 1;
    items[1].b = 5;
    return items[1].b;
}

uint8_t byte_view(void) {
    uint8_t buf[4];
    buf[2] = 7;
    unsigned char *b = buf;
    return b[2];
}
```

```click
verifying "own.c";

int32 ptrs_own(int32 **a) {
    views a[0..1];
    ensures true;
} by {
    execute();
}

int32 local_cell() {
    ensures result == 3;
} by {
    execute();
    simp();
}

long struct_array() {
    ensures result == 5;
} by {
    execute();
    simp();
}

uint8 byte_view() {
    ensures result == 7u8;
} by {
    execute();
    simp();
}
```

```expect
pass
```
