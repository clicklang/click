# Known machine observation primitives

Each identity consumes only its written operator and explicit range or guard facts.

```click
theorem native_ranges(x: int32, y: uint32) {
    ensures x <= 2147483647 by known();
    ensures -2147483648 <= x by known();
    ensures 0u32 <= y by known();
    ensures y <= 4294967295u32 by known();
}
theorem intrinsic(x: uint64) {
    ensures 0 <= to_integer(x) by known();
    ensures to_integer(x) <= 18446744073709551615 by known();
}
theorem operation(x: uint32, y: uint32) {
    requires 0 <= to_integer(x) + to_integer(y);
    requires to_integer(x) + to_integer(y) <= 4294967295;
    ensures to_integer(x + y) == to_integer(x) + to_integer(y) by known();
}
theorem conversion(x: Integer) {
    requires -128 <= x;
    requires x <= 127;
    ensures to_integer(to_int8(x)) == x by known();
}
theorem conditional(x: Integer, y: Integer) {
    requires x < y;
    ensures (if x < y { x } else { y }) == x by known();
}
theorem mask(x: int32) {
    ensures (x & 255) <= 255 by known();
}
```

```expect
pass
```
