# Explicit pointer translation and association laws

Pointer translation needs a pointer relation and exact Integer displacements.
The association helpers additionally expose signed/unsigned addition guards.

```click
theorem translated_i32(p: int32*, q: int32*, a: int32, b: int32, c: int32, d: int32) {
    requires p + a == q + b;
    requires to_integer(c) - to_integer(a) == to_integer(d) - to_integer(b);
    ensures p + c == q + d by {
        apply(integer::int32_pointer_translate_int32(p, q, a, b, c, d)) using {
            p + a == q + b;
            to_integer(c) - to_integer(a) == to_integer(d) - to_integer(b);
        };
    }
}
theorem translated_u64(p: uint64*, q: uint64*, a: uint64, b: uint64, c: uint64, d: uint64) {
    requires p + a == q + b;
    requires to_integer(c) - to_integer(a) == to_integer(d) - to_integer(b);
    ensures p + c == q + d by {
        apply(integer::uint64_pointer_translate_uint64(p, q, a, b, c, d)) using {
            p + a == q + b;
            to_integer(c) - to_integer(a) == to_integer(d) - to_integer(b);
        };
    }
}
theorem associated_i32(p: const uint8*, i: int32, j: int32) {
    requires defined(i + j);
    ensures (p + i) + j == p + (i + j) by {
        apply(integer::uint8_pointer_add_associate_int32(p, i, j)) using { defined(i + j); };
    }
}
theorem associated_u64(p: int16*, i: uint64, j: uint64) {
    requires to_integer(i) + to_integer(j) <= 18446744073709551615;
    ensures (p + i) + j == p + (i + j) by {
        apply(integer::int16_pointer_add_associate_uint64(p, i, j)) using {
            to_integer(i) + to_integer(j) <= 18446744073709551615;
        };
    }
}
```

```expect
pass
```
