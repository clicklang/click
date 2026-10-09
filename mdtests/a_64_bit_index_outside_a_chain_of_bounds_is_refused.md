# A 64-bit index outside a chain of bounds is refused

`get` reads `bytes[i]` with `i < n`, and `n` is bounded by `m`, which is
not `length`. No chain of order facts reaches `length` from `i`, so forming
`bytes + i` is not shown to stay inside the range the contract holds, and
the pointer arithmetic is refused.

`a_64_bit_index_is_in_range_through_a_chain_of_bounds.md` completes the
chain.

```c filename=a_64_bit_index_outside_a_chain_of_bounds_is_refused.c
unsigned char get(const unsigned char *bytes, unsigned long length, unsigned long n, unsigned long m, unsigned long i) {
    return bytes[i];
}
```

```click
verifying "a_64_bit_index_outside_a_chain_of_bounds_is_refused.c";
uint8 get(const uint8* bytes, uint64 length, uint64 n, uint64 m, uint64 i) {
    requires n <= m;
    requires i < n;
    views bytes[0..length];
    ensures result == result;
} by { execute(); simp(); }
```

```expect
fail: pointer arithmetic left the pointed-to object
```
