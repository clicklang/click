# induct refuses an Integer parameter

Scalar induction is over an `int32` or `uint64` parameter. `induct(n)` on an
`Integer` parameter is refused with that reason.

```c filename=induct_refuses_an_integer_parameter.c
void unused(void) {}
```

```click
verifying "induct_refuses_an_integer_parameter.c";

theorem over_integer(n: Integer) {
    requires n >= 0;
    ensures n == n by {
        induct(n) as ih;
        normalize();
    }
}
```

```expect
fail: `induct(n)` requires an int32 or uint64 theorem parameter with that name
```
