# Converting NaN to an integer has undefined behavior

```c filename=cast.c
int32 convert(void) { return (int32)(0.0 / 0.0); }
```

```click
verifying "cast.c";

int32 convert() {
    ensures true;
}
```

```expect
fail: undefined behavior: float-to-integer conversion is out of range
```
