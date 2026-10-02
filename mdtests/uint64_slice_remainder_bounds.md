# A bounded slice split leaves a positive suffix length

Unsigned subtraction is interpreted at full width. An explicit order premise
establishes both nonempty remainder and its upper bound without wrapping.

```c filename=uint64_slice_remainder_bounds.c
unsigned long remainder(unsigned long length, unsigned long mid) {
    return length - mid;
}
```

```click
verifying "uint64_slice_remainder_bounds.c";
uint64 remainder(uint64 length, uint64 mid) {
    requires mid < length;
    requires mid <= length;
    ensures result == length - mid;
} by {
    have 0u64 < length - mid by { normalize() using { mid < length; } }
    have length - mid <= length by { normalize() using { mid <= length; } }
    execute(); simp();
}
```

```expect
pass
```
