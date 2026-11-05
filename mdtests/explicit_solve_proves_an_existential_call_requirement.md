# The same solver proves an existential call requirement

```c filename=call.c
int32 caller(int32 a) { return callee(a); }
```

```click
verifying "call.c";
extern int32 callee(int32 x) {
    requires exists (witness: int32) { witness >= 0 };
    ensures result == x;
}
int32 caller(int32 a) {
    ensures result == a;
} by {
    step() by solve();
    step(); solve();
}
```

```expect
pass
```
