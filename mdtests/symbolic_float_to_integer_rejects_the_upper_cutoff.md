# Equality at the upper cutoff refutes a signed cast's strict bound

```c filename=cast.c
int32 convert(double x) { return (int32)x; }
```

```click
verifying "cast.c";

int32 convert(double x) {
    requires x == float64_from_bits(0x41e0000000000000u64);
    ensures true;
}
```

```expect
fail: undefined behavior: float-to-integer conversion is out of range
```
