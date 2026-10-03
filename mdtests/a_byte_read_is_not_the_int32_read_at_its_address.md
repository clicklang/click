# a byte read is not the int32 read at its address

`u[4 * i]` is the low byte of the `int32` `q[i]`. The two are equal only when
the upper three bytes are zero, so `result == 1` is false (`q[i] == 256` has a
low byte of `0`).

That claim was **provable**, by two routes at once. Both reads named one load
term, because a term did not say how many bytes it read. And the int32
equality graph took every load variable whose recorded width was four bytes as
an int32 read, but the recorded width is the widest access seen at the
address, so the byte read qualified as soon as `q[i]` was read beside it. A
load term now carries its read's kind, and only a four-byte integer read is an
int32 load in the graph.

`a_signed_and_an_unsigned_byte_read_are_two_values.md` is the same hole at
one width, and `a_byte_result_is_not_the_int32_it_lands_in.md` is this one in
a contract.

```c filename=a_byte_read_is_not_the_int32_read_at_its_address.c
#include <stdint.h>

int low_byte(int32_t* q, int i) {
    unsigned char* u;
    u = (unsigned char*)(void*) q;
    return q[i] == u[4 * i];
}
```

```click
verifying "a_byte_read_is_not_the_int32_read_at_its_address.c";

int low_byte(int32_t* q, int i) {
    requires i >= 0;
    requires i < 4;
    views q[0..4];
    ensures result == 1;
} by {
    execute();
    simp();
}
```

```expect
fail: `ensures result == 1` failed for `low_byte.ensures_0`
```
