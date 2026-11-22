# An outcome proof guard can read a preceding obtain

```c filename=obtain_guard.c
int use_obtain(int n) { return n; }
```

```click
verifying "obtain_guard.c";

int32 use_obtain(int32 n) {
    requires (0..n).any(|i| { i != 1 });
    ensures exists (k: int32) { k < result };
} by {
    step_until(function.exit);
    let k = obtain((0..n).any(|i| { i != 1 }));
    have 0 <= k by known();
    have k != 1 by known();
    if k < n {
        have k < n by known();
    } else {
        have false by known();
    }
    if result == n {
        let j = obtain(at(function.entry, (0..n).any(|j| { j != 1 })));
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
