# A verified call proves separation from a caller borrow at entry

The call's write effect and the active view give the step its proof goal.
The caller's resource partition establishes their separation.

```c filename=verified_call_write_separation.c
void set_cell(int *target) { *target = 7; }
void write_beside_view(int *target, const int *viewed) {
    set_cell(target);
}
```

```click
verifying "verified_call_write_separation.c";

void set_cell(int *target) {
    owns target[0..1];
}

void write_beside_view(int *target, const int *viewed) {
    owns target[0..1];
    views viewed[0..1];
} by {
    step() by { solve(); }
}
```

```expect
pass
```
