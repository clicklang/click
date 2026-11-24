```c filename=beta_unused_binder.c
int f(void) { return 3; }
```
```click
verifying "beta_unused_binder.c";
int32 f() {
    ensures result == (|x: int32| -> int32 { let unused: int32 = 0; x })(3) by {
        step_until(function.exit);
        solve();
    }
    ensures result == (|x: int32| -> int32 { let unused: int32 = 0; x })(3) by {
        step_until(function.exit);
        solve();
    }
}
```
```expect
pass
```
