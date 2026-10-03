# An outer lvalue that calls a function stays rejected beside an assignment

A call in the lvalue and the inner assignment are two unsequenced side effects.

```c filename=c_chained_assignment_lvalue_call_rejected.c
int slot(int key);

int32 run(int *table, int key, int value) {
    int copy;
    table[slot(key)] = copy = value;
    return copy;
}
```

```click
verifying "c_chained_assignment_lvalue_call_rejected.c";

```

```expect
fail:c_chained_assignment_lvalue_call_rejected.c:5: multiple unsequenced expression side effects are not supported
```
