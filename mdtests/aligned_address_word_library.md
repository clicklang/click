# Explicit aligned address-word library applications

Each word and pointer-offset law has a direct application with its exact guards.

```click
import click::integer;

theorem use_uint64_and_commute(a: uint64, b: uint64) {
    ensures (a & b) == (b & a) by {
        apply(integer::uint64_and_commute(a, b)) using { };
    }
}

theorem use_uint64_and_associate(a: uint64, b: uint64, c: uint64) {
    ensures ((a & b) & c) == (a & (b & c)) by {
        apply(integer::uint64_and_associate(a, b, c)) using { };
    }
}

theorem use_uint64_or_commute(a: uint64, b: uint64) {
    ensures (a | b) == (b | a) by {
        apply(integer::uint64_or_commute(a, b)) using { };
    }
}

theorem use_uint64_and_or(a: uint64, b: uint64, mask: uint64) {
    ensures ((a | b) & mask) == ((a & mask) | (b & mask)) by {
        apply(integer::uint64_and_or(a, b, mask)) using { };
    }
}

theorem use_uint64_and_zero(a: uint64) {
    ensures (a & 0u64) == 0u64 by {
        apply(integer::uint64_and_zero(a)) using { };
    }
}

theorem use_uint64_or_zero(a: uint64) {
    ensures (a | 0u64) == a by {
        apply(integer::uint64_or_zero(a)) using { };
    }
}

theorem use_uint64_or_disjoint(a: uint64, b: uint64) {
    requires (a & b) == 0u64;
    ensures (a | b) == ((a + b) as uint64) by {
        apply(integer::uint64_or_disjoint(a, b)) using { (a & b) == 0u64; };
    }
}

theorem use_uint64_mask_add_low(base: uint64, tag: uint64, mask: uint64) {
    requires (mask & (mask + 1u64)) == 0u64;
    requires (base & mask) == 0u64;
    ensures ((base + tag) & mask) == (tag & mask) by {
        apply(integer::uint64_mask_add_low(base, tag, mask)) using { (mask & (mask + 1u64)) == 0u64; (base & mask) == 0u64; };
    }
}

theorem use_uint64_mask_add_high(base: uint64, tag: uint64, mask: uint64) {
    requires ((~mask) & ((~mask) + 1u64)) == 0u64;
    requires (base & (~mask)) == 0u64;
    ensures ((base + tag) & mask) == ((base + (tag & mask)) as uint64) by {
        apply(integer::uint64_mask_add_high(base, tag, mask)) using { ((~mask) & ((~mask) + 1u64)) == 0u64; (base & (~mask)) == 0u64; };
    }
}

theorem use_uint64_mask_multiple(value: uint64, factor: uint64, mask: uint64) {
    requires (mask & (mask + 1u64)) == 0u64;
    requires (factor & mask) == 0u64;
    ensures ((value * factor) & mask) == 0u64 by {
        apply(integer::uint64_mask_multiple(value, factor, mask)) using { (mask & (mask + 1u64)) == 0u64; (factor & mask) == 0u64; };
    }
}

theorem use_uint64_mask_keep(base: uint64, mask: uint64) {
    requires (base & (~mask)) == 0u64;
    ensures (base & mask) == base by {
        apply(integer::uint64_mask_keep(base, mask)) using { (base & (~mask)) == 0u64; };
    }
}

theorem use_uint64_mask_add_clear(base: uint64, tag: uint64, mask: uint64) {
    requires ((~mask) & ((~mask) + 1u64)) == 0u64;
    requires (base & (~mask)) == 0u64;
    requires (tag & mask) == 0u64;
    ensures ((base + tag) & mask) == base by {
        apply(integer::uint64_mask_add_clear(base, tag, mask)) using { ((~mask) & ((~mask) + 1u64)) == 0u64; (base & (~mask)) == 0u64; (tag & mask) == 0u64; };
    }
}

theorem use_uint64_add_distinct(base: uint64, a: uint64, b: uint64) {
    requires a != b;
    ensures ((base + a) as uint64) != ((base + b) as uint64) by {
        apply(integer::uint64_add_distinct(base, a, b)) using { a != b; };
    }
}

theorem use_uint64_or_add_low(base: uint64, tag: uint64, bits: uint64, mask: uint64) {
    requires (mask & (mask + 1u64)) == 0u64;
    requires (base & mask) == 0u64;
    requires (bits & mask) == bits;
    ensures ((base + tag) | bits) == ((base + (tag | bits)) as uint64) by {
        apply(integer::uint64_or_add_low(base, tag, bits, mask)) using { (mask & (mask + 1u64)) == 0u64; (base & mask) == 0u64; (bits & mask) == bits; };
    }
}

theorem use_uint64_mask_subset(base: uint64, large: uint64, small: uint64) {
    requires (base & large) == 0u64;
    requires (large & small) == small;
    ensures (base & small) == 0u64 by {
        apply(integer::uint64_mask_subset(base, large, small)) using { (base & large) == 0u64; (large & small) == small; };
    }
}

theorem use_uint64_or_masked(base: uint64, tag: uint64, mask: uint64) {
    requires (base & mask) == 0u64;
    ensures (base | (tag & mask)) == ((base + (tag & mask)) as uint64) by {
        apply(integer::uint64_or_masked(base, tag, mask)) using { (base & mask) == 0u64; };
    }
}

theorem use_uint8_pointer_add_address_int32(p: uint8*, index: int32) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 1u64) as uint64) by {
        apply(integer::uint8_pointer_add_address_int32(p, index)) using { };
    }
}

theorem use_uint8_pointer_add_address_int64(p: uint8*, index: int64) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 1u64) as uint64) by {
        apply(integer::uint8_pointer_add_address_int64(p, index)) using { };
    }
}

theorem use_int8_pointer_add_address_int32(p: int8*, index: int32) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 1u64) as uint64) by {
        apply(integer::int8_pointer_add_address_int32(p, index)) using { };
    }
}

theorem use_int8_pointer_add_address_int64(p: int8*, index: int64) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 1u64) as uint64) by {
        apply(integer::int8_pointer_add_address_int64(p, index)) using { };
    }
}

theorem use_uint16_pointer_add_address_int32(p: uint16*, index: int32) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 2u64) as uint64) by {
        apply(integer::uint16_pointer_add_address_int32(p, index)) using { };
    }
}

theorem use_uint16_pointer_add_address_int64(p: uint16*, index: int64) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 2u64) as uint64) by {
        apply(integer::uint16_pointer_add_address_int64(p, index)) using { };
    }
}

theorem use_int16_pointer_add_address_int32(p: int16*, index: int32) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 2u64) as uint64) by {
        apply(integer::int16_pointer_add_address_int32(p, index)) using { };
    }
}

theorem use_int16_pointer_add_address_int64(p: int16*, index: int64) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 2u64) as uint64) by {
        apply(integer::int16_pointer_add_address_int64(p, index)) using { };
    }
}

theorem use_uint32_pointer_add_address_int32(p: uint32*, index: int32) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 4u64) as uint64) by {
        apply(integer::uint32_pointer_add_address_int32(p, index)) using { };
    }
}

theorem use_uint32_pointer_add_address_int64(p: uint32*, index: int64) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 4u64) as uint64) by {
        apply(integer::uint32_pointer_add_address_int64(p, index)) using { };
    }
}

theorem use_int32_pointer_add_address_int32(p: int32*, index: int32) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 4u64) as uint64) by {
        apply(integer::int32_pointer_add_address_int32(p, index)) using { };
    }
}

theorem use_int32_pointer_add_address_int64(p: int32*, index: int64) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 4u64) as uint64) by {
        apply(integer::int32_pointer_add_address_int64(p, index)) using { };
    }
}

theorem use_uint64_pointer_add_address_int32(p: uint64*, index: int32) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 8u64) as uint64) by {
        apply(integer::uint64_pointer_add_address_int32(p, index)) using { };
    }
}

theorem use_uint64_pointer_add_address_int64(p: uint64*, index: int64) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 8u64) as uint64) by {
        apply(integer::uint64_pointer_add_address_int64(p, index)) using { };
    }
}

theorem use_int64_pointer_add_address_int32(p: int64*, index: int32) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 8u64) as uint64) by {
        apply(integer::int64_pointer_add_address_int32(p, index)) using { };
    }
}

theorem use_int64_pointer_add_address_int64(p: int64*, index: int64) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 8u64) as uint64) by {
        apply(integer::int64_pointer_add_address_int64(p, index)) using { };
    }
}

theorem use_float32_pointer_add_address_int32(p: float*, index: int32) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 4u64) as uint64) by {
        apply(integer::float32_pointer_add_address_int32(p, index)) using { };
    }
}

theorem use_float32_pointer_add_address_int64(p: float*, index: int64) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 4u64) as uint64) by {
        apply(integer::float32_pointer_add_address_int64(p, index)) using { };
    }
}

theorem use_float64_pointer_add_address_int32(p: double*, index: int32) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 8u64) as uint64) by {
        apply(integer::float64_pointer_add_address_int32(p, index)) using { };
    }
}

theorem use_float64_pointer_add_address_int64(p: double*, index: int64) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 8u64) as uint64) by {
        apply(integer::float64_pointer_add_address_int64(p, index)) using { };
    }
}
```

```expect
pass
```
