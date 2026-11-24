# Obtain an established existential at function exit

The binding is available after the first `close()` closes the ownership claim.

```c filename=obtain_focus.c
int obtain_at_exit(int *p, int n) { return n; }
```

```click
verifying "obtain_focus.c";

int32 obtain_at_exit(int32* p, int32 n) {
    requires exists (k: int32) { k < n };
    owns *p;
    ensures exists (k: int32) { k < result };
} by {
    step_until(function.exit);
    let k = obtain(exists (k: int32) { k < n });
    close();
    witness(k);
    close();
}
```

```expect
pass
```
