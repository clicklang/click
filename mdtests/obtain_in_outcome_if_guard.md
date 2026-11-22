# An outcome proof guard can read a preceding obtain

```c filename=obtain_guard.c
int use_obtain(int n) { return n; }
```

```click
verifying "obtain_guard.c";

int32 use_obtain(int32 n) {
    requires exists (k: int32) { k < n };
    ensures exists (k: int32) { k < result };
} by {
    step_until(function.exit);
    let k = obtain(exists (k: int32) { k < n });
    if k < n {
        have k < n by known();
    } else {
        have false by known();
    }
    if result == n {
        let j = obtain(exists (j: int32) { j < n });
        if j >= n {
            have false by known();
        } else {
            have j < n by known();
        }
    } else {
        have false by known();
    }
    witness(k);
    solve();
}
```

```expect
pass
```
