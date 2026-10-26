# The implicit closer proves a 64-bit equality from bounds

The implicit closer proves an order between 64-bit values by its `Integer` reading and
the type's bridge back. An equality goes the same way: `x == 0u64` follows
from `not 0u64 < x` because `to_integer(x) == 0` does, and
`integer::uint64_to_integer_equal_implies_equal` carries that back. The kernel's
64-bit equality does not record a signedness, so the implicit closer tries the `uint64`
bridge and then the `int64` one, after its cheaper searches miss. A
`have` and a theorem's claim each prove it with the proof omitted.

```c filename=auto_proves_a_64_bit_equality_from_bounds.c
void unsigned_at_zero(unsigned long x) {
}

void signed_pinned(long a, long b) {
}
```

```click
verifying "auto_proves_a_64_bit_equality_from_bounds.c";

void unsigned_at_zero(uint64 x) {
    requires not 0u64 < x;
    ensures x == 0u64;
} by {
    have x == 0u64;
}

theorem unsigned_at_zero_by_auto(x: uint64) {
    requires not 0u64 < x;
    ensures x == 0u64;
}

void signed_pinned(int64 a, int64 b) {
    requires a <= b;
    requires b <= a;
    ensures a == b;
} by {
    have a == b;
}
```

```expect
pass
```
