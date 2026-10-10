# Separation of an array also separates its last element

The descriptor field occupies eight bytes and the array's elements occupy four.
Narrowing the array footprint preserves their stated byte separation.

```click
theorem last_element_separate(field: uint64*, data: int32*, n: int32) {
    requires 1 <= n;
    requires n <= 1073741823;
    requires separate(memory(*field), memory(data[0..n]));
    ensures separate(memory(*field), memory(data[n - 1])) by {
        have 0 <= n - 1 by { arithmetic() using { 1 <= n; n <= 1073741823; } }
        have n - 1 < n by { arithmetic() using { 1 <= n; n <= 1073741823; } }
        have separate(memory(*field), memory(data[n - 1])) by assumption();
        assumption();
    }
}
```

```expect
pass
```
