# Compare exact machine conversions of an observed read

The range of the observed read makes its conversion defined. Comparing the
converted value with itself keeps the same read on both sides.

```c filename=identity.c
int identity(int *p) { return p[0]; }
```

```click
verifying "identity.c";

int32 identity(int32 *p) {
    views p[0..1];
    requires 0 <= p[0];
    ensures result == p[0];
} by {
    have to_uint32(to_integer(p[0])) == to_uint32(to_integer(p[0])) by { close(); }
    step_until(function.exit);
}
```

```expect
pass
```
