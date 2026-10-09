# A 64-bit index is in range through a chain of bounds

`get` reads `bytes[i]`. The contract does not bound `i` by `length`
directly: `i < n` and `n <= length`. The kernel follows the chain of 64-bit
order facts from `i` to `length`, as it does for `int`.

`a_64_bit_index_outside_a_chain_of_bounds_is_refused.md` breaks the chain.

```c filename=a_64_bit_index_is_in_range_through_a_chain_of_bounds.c
unsigned char get(const unsigned char *bytes, unsigned long length, unsigned long n, unsigned long i) {
    return bytes[i];
}
long get_signed(const long *cells, long length, long n, long i) {
    return cells[i];
}
```

```click
verifying "a_64_bit_index_is_in_range_through_a_chain_of_bounds.c";
uint8 get(const uint8* bytes, uint64 length, uint64 n, uint64 i) {
    requires length <= 2147483647u64;
    requires n <= length;
    requires i < n;
    views bytes[0..length];
    ensures result == bytes[i];
} by { execute(); simp(); }
int64 get_signed(const int64* cells, int64 length, int64 n, int64 i) {
    requires length <= 1000i64;
    requires n <= length;
    requires 0i64 <= i;
    requires i < n;
    views cells[0..length];
    ensures result == result;
} by { execute(); simp(); }
```

```expect
pass
```
