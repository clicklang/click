# Range-checked legacy cast observations

Ordinary casts and the shared modulo conversion boundary retain their existing
32/64-bit terms. Exact observation requires two explicit destination-range
bounds. These casts include Bitcoin's fast-path fee, amount and denominator
conversions.

```click
theorem cast0(value: int64) {
    requires 0 <= to_integer(value);
    requires to_integer(value) <= 8589934591;
    ensures to_integer(value as uint64) == to_integer(value) by {
        close() using { 0 <= to_integer(value); to_integer(value) <= 8589934591; };
    }
}
theorem cast1(value: int32) {
    requires 0 <= to_integer(value);
    requires to_integer(value) <= 2147483647;
    ensures to_integer(value as uint64) == to_integer(value) by {
        close() using { 0 <= to_integer(value); to_integer(value) <= 2147483647; };
    }
}
theorem cast2(value: int32) {
    requires 1 <= to_integer(value);
    requires to_integer(value) <= 2147483647;
    ensures to_integer(value as uint32) == to_integer(value) by {
        close() using { 1 <= to_integer(value); to_integer(value) <= 2147483647; };
    }
}
theorem cast3(value: uint32) {
    requires 0 <= to_integer(value);
    requires to_integer(value) <= 4294967295;
    ensures to_integer(value as uint64) == to_integer(value) by {
        close() using { 0 <= to_integer(value); to_integer(value) <= 4294967295; };
    }
}
```

```expect
pass
```
