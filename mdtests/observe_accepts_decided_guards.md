# Observation accepts either decided guard

The active resource exposes its body. The inactive resource has an empty
body and can also be observed.

```c filename=observe_accepts_decided_guards.c
int32 active(int32 enabled, int32 value) { return value; }
int32 inactive(int32 enabled, int32 value) { return 0; }
```

```click
abstract resource marker();

resource guarded(flag: int32, value: int32) {
    if flag != 0 {
        owns marker();
        fact value >= 0;
    }
}

verifying "observe_accepts_decided_guards.c";

int32 active(int32 enabled, int32 value) {
    owns guarded(enabled, value);
    requires enabled != 0;
    ensures result >= 0;
} by {
    observe(guarded(enabled, value));
    step_until(function.exit);
}

int32 inactive(int32 enabled, int32 value) {
    owns guarded(enabled, value);
    requires enabled == 0;
    ensures result == 0;
} by {
    observe(guarded(enabled, value));
    step_until(function.exit);
}
```

```expect
pass
```
