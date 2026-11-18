# Printed float-cast bounds can be reused as contract prerequisites

```c filename=branch_float_cast.c
int32 positive(double d) {
    if ((int32) d > 0) {
        return 1;
    }
    return 0;
}
```

```click
verifying "branch_float_cast.c";

int32 positive(double d) {
    requires isfinite(d);
    requires d >= float64_from_bits(0xc1e0000000000000u64);
    requires d < float64_from_bits(0x41e0000000000000u64);
    ensures result >= 0;
} by {
    branch { true => { step(); solve(); } false => {} }
    step();
    solve();
}
```

```expect
pass
```
