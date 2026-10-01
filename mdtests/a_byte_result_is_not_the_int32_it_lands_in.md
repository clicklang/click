# a byte result is not the int32 it lands in

The body returns the low byte of `q[i]`; the contract claims it returns all of
`q[i]`. The claim was **provable**, because the byte read and the `int32` read
of the contract named one load term. They are now two terms, and the refusal
says why the two sides differ: not a store between them, but two kinds of
read of one address.

`a_byte_read_is_not_the_int32_read_at_its_address.md` is the same hole inside
one body.

```c filename=a_byte_result_is_not_the_int32_it_lands_in.c
#include <stdint.h>

int low_byte(int32_t* q, int i) {
    unsigned char* u;
    u = (unsigned char*)(void*) q;
    return u[4 * i];
}
```

```click
verifying "a_byte_result_is_not_the_int32_it_lands_in.c";

int low_byte(int32_t* q, int i) {
    requires i >= 0;
    requires i < 4;
    views q[0..4];
    ensures result == q[i];
} by {
    execute();
    simp();
}
```

```expect
fail: the two sides read `q[i]` as different kinds of value, the left as an unsigned byte and the right as a four-byte word
```
