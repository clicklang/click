# A contract call names its effect point

A call to a function with a contract makes its effects in two steps of one
region. First every value the call writes is in place: the callee's
footprint holds its new values. Then the call's effects on initialization,
liveness and allocation are applied, which reach its exit. The state between
them is the call's `.effect` point, `call(set, 0).effect`.

Every value is the same at `.effect` as at `.exit`, so the value `set` wrote
can be read at either. `.effect` is a migration measure: a read the call
makes before its exit is named there until reads are named by the write that
made their value.

```c filename=effect_point.c
void set(int32 *p) {
    *p = 7;
}

int32 caller(int32 *p) {
    set(p);
    return *p;
}
```

```click
verifying "effect_point.c";

void set(int32 *p) {
    owns *p;
    ensures *p == 7;
}

int32 caller(int32 *p) {
    owns *p;
    ensures result == 7;
} by {
    step();
    have at(call(set, 0).effect, *p) == 7 by close();
    have at(call(set, 0).exit, *p) == 7 by close();
    step_until(function.exit);
}
```

```expect
pass
```
