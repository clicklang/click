# Bounded unsigned fields pack without overlap or lost high bits

Both field bounds are required. The result is an Integer observation of the
actual bitwise OR and shift, rather than an assumed checksum formula.

```click
import click::integer;

theorem pack32(low: uint32, high: uint32) {
    requires low <= 65535u32;
    requires high <= 65535u32;
    ensures to_integer(low | (high << 16)) == to_integer(low) + 65536 * to_integer(high) by {
        apply(uint32_pack_uint16_to_integer(low, high)); assumption();
    }
}
theorem pack64(low: uint64, high: uint64) {
    requires low <= 65535u64;
    requires high <= 65535u64;
    ensures to_integer(low | (high << 16)) == to_integer(low) + 65536 * to_integer(high) by {
        apply(uint64_pack_uint16_to_integer(low, high)); assumption();
    }
}
theorem order_complement(left: uint64, right: uint64) {
    requires left < right;
    ensures not(left >= right) by {
        apply(uint64_less_than_implies_not_greater_equal(left, right)); assumption();
    }
}
```

```expect
pass
```
