# An Integer converted to a machine type reads back

A specification computes a byte count as an `Integer` and converts it to the
`size_t` a C function returns. Under the count's range, `to_integer` of the
conversion is the count: `integer_cast_identity` reads
`to_integer(to_uint64(z))` as `z` from `z`'s two bounds inside `uint64`'s
range, stated once for every format, and the omitted proof plans it with no
library law in scope. The second theorem converts at `int8` and the third at
`uint128`, which has no operations but has the conversion. The last is
refused before any proof: without the upper bound, `to_uint8(z)` owes `z`'s
range where it is stated, so the identity is never read for a `z` outside
it.

```c filename=bytes.c
#include <stdint.h>
#include <stddef.h>

size_t byte_count(size_t n) {
    return n * 4;
}
```

```click
verifying "bytes.c";

size_t byte_count(size_t n) {
    requires to_integer(n) <= 1000;
    ensures to_integer(result) == to_integer(to_uint64(4 * to_integer(n)));
}

theorem byte_count_reads_back(z: Integer) {
    requires 0 <= z;
    requires z <= 4000;
    ensures to_integer(to_uint64(z)) == z;
}

theorem signed_byte_reads_back(z: Integer) {
    requires -128 <= z;
    requires z <= 127;
    ensures to_integer(to_int8(z)) == z;
}

theorem wide_reads_back(z: Integer) {
    requires 0 <= z;
    requires z <= 340282366920938463463374607431768211455;
    ensures to_integer(to_uint128(z)) == z;
}

theorem unbounded_does_not_read_back(z: Integer) {
    requires 0 <= z;
    ensures to_integer(to_uint8(z)) == z;
}
```

```expect
fail: the Integer converted back to a machine type must fit it
```
