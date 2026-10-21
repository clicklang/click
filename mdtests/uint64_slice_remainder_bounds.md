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
    ensures to_integer(result) == to_integer(length - mid);
} by {
    have to_integer(0u64) < to_integer(length - mid) by { normalize() using { mid < length; }; }
    have to_integer(length - mid) <= to_integer(length) by { normalize() using { mid <= length; }; }
    execute(); simp();
}
```

```expect
pass
```
