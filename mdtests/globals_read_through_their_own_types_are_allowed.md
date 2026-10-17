# Globals read through their own types are allowed

A global `long` read through a `long *`, a global struct's member, and a
byte of a global `uint8_t` array keep their declared types and verify.

```c filename=globals.c
#include <stdint.h>
struct a { int x; };
long counter;
uint8_t buffer[4];
struct a shared;

long read_counter(void) {
    long *p = &counter;
    return *p;
}

int read_shared(void) {
    struct a *p = &shared;
    return p->x;
}

uint8_t read_byte(void) {
    unsigned char *b = buffer;
    return b[1];
}
```

```click
verifying "globals.c";

long read_counter() {
    owns counter;
    ensures result == counter;
} by {
    execute();
    simp();
}

int32 read_shared() {
    owns shared.x;
    ensures result == shared.x;
} by {
    execute();
    simp();
}

uint8 read_byte() {
    owns buffer[0..4];
    ensures result == buffer[1];
} by {
    execute();
    simp();
}
```

```expect
pass
```
