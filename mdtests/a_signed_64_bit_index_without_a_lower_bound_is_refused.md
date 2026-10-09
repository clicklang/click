# A signed 64-bit index without a lower bound is refused

`get` reads `cells[i]` with a `long` index bounded above only. `i` may be
negative, which reads before the range.

`a_64_bit_index_is_in_range_through_a_chain_of_bounds.md` has the signed
read with both bounds.

```c filename=a_signed_64_bit_index_without_a_lower_bound_is_refused.c
long get(const long *cells, long i) {
    return cells[i];
}
```

```click
verifying "a_signed_64_bit_index_without_a_lower_bound_is_refused.c";
int64 get(const int64* cells, int64 i) {
    requires i < 8i64;
    views cells[0..8];
    ensures result == result;
} by { execute(); simp(); }
```

```expect
fail: missing resource fact
```
