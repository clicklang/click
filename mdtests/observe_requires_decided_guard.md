# Observation requires a decided guard

The held resource has a guarded body. Its ownership alone does not decide
whether the body is present. Explicit observation identifies the missing
condition using the caller's argument name.

```c filename=observe_requires_decided_guard.c
int32 probe(int32 enabled) { return 0; }
```

```click
resource guarded(flag: int32) {
    if flag != 0 {
        fact flag == 1;
    }
}

verifying "observe_requires_decided_guard.c";

int32 probe(int32 enabled) {
    owns guarded(enabled);
    ensures result == 0;
} by {
    observe(guarded(enabled));
    step_until(function.exit);
}
```

```expect
fail: guard `enabled != 0` is undecided
```
