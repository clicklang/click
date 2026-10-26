# Click proposition logic

This checks Click proposition syntax in a sidecar proof. The logical words
`and`, `not`, and `implies` are Click syntax, distinct from C-fragment
operators.

```c filename=identity_prop.c
int32 identity_prop(int32 x) {
    return x;
}
```

```click
verifying "identity_prop.c";

int32 identity_prop(int32 x) {
    requires x >= 0;
    ensures prop_logic: result == x and not (result != x);
    ensures prop_implies: result == x implies result >= 0;
}
```

```expect
pass
```
