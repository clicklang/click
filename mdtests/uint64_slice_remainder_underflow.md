# A wrapping subtraction cannot supply a suffix length bound

```c filename=uint64_slice_remainder_underflow.c
unsigned long remainder(unsigned long length, unsigned long mid) {
    return length - mid;
}
```

```click
verifying "uint64_slice_remainder_underflow.c";
uint64 remainder(uint64 length, uint64 mid) {
    requires length == 1u64;
    requires mid == 2u64;
    ensures result == length - mid;
} by {
    have length - mid <= length by { normalize() using { length == 1u64; mid == 2u64; } }
    execute(); simp();
}
```

```expect
fail: normalize using
```
