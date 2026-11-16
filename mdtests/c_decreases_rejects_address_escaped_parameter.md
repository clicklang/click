# a recursive termination measure cannot escape through a parameter address

The body writes 1000 through `&n`, so the recursive call passes 999.
Its guard establishes only that the entry value was positive; it cannot prove
999 is smaller than that entry value. The ordinary call obligation refuses
this nondecreasing recursion, rather than banning parameter addresses.

```c filename=c_decreases_rejects_address_escaped_parameter.c
int32 escaped_parameter(int32 n) {
    int32* p;
    p = &n;
    if (n > 0) {
        *p = 1000;
        escaped_parameter(n - 1);
    }
    return 0;
}
```

```click
verifying "c_decreases_rejects_address_escaped_parameter.c";

int32 escaped_parameter(int32 n) {
    decreases n;
    ensures result == 0;
}
```

```expect
fail: escaped_parameter recursion measure: `n` decreases at the recursive call
```
