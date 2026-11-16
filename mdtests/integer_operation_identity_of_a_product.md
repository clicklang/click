# `integer_operation_identity` observes a product inside its type

Arithmetic search expands to ordinary proof steps, with the selected premises
stated explicitly in `solve() using { ... }`.

```click
theorem bounded(x: uint32) {
    requires x <= 1000u32;
    ensures to_integer(x * 2u32) == to_integer(x) * 2 by {
        have 0 <= to_integer(x) * 2;
        have to_integer(x) * 2 <= 4294967295;
        solve() using { 0 <= to_integer(x) * 2; to_integer(x) * 2 <= 4294967295; };
    };
}
```

```expect
pass
```
