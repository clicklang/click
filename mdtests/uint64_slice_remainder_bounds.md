# A bounded slice split leaves a positive suffix length

Unsigned subtraction is interpreted at full width. An explicit order premise
establishes both nonempty remainder and its upper bound without wrapping.

```c filename=uint64_slice_remainder_bounds.c
unsigned long remainder(unsigned long length, unsigned long mid) {
    return length - mid;
}
```

```click
import click::integer;
verifying "uint64_slice_remainder_bounds.c";
uint64 remainder(uint64 length, uint64 mid) {
    requires mid < length;
    requires mid <= length;
    ensures to_integer(result) == to_integer(length - mid);
} by {
    have to_integer(0u64) < to_integer(length - mid) by {
        have to_integer(mid) < to_integer(length) by close() using { mid < length; };
        have to_integer(mid) <= to_integer(length) by close() using { to_integer(mid) < to_integer(length); };
        apply(integer::uint64_subtract_to_integer(length, mid));
        rewrite(to_integer(length - mid), to_integer(length) - to_integer(mid));
        close() using { to_integer(mid) < to_integer(length); };
    }
    have to_integer(length - mid) <= to_integer(length) by {
        have to_integer(mid) <= to_integer(length) by close() using { mid <= length; };
        apply(integer::uint64_subtract_to_integer(length, mid));
        rewrite(to_integer(length - mid), to_integer(length) - to_integer(mid));
        have 0 <= to_integer(mid) by close();
        close() using { 0 <= to_integer(mid); };
    }
}
```

```expect
pass
```
