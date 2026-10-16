# A false `transport` in a `branch` arm is refused as on the main line

A written `transport(source, target)` that the source-local frame check cannot
carry falls back to the checked premise planner. The main proof line always
did that, so a false target is refused with the planner's reason. An
execution arm used to try only the source-local form and then decline the
whole proof shape, so the same false transport inside `branch` was reported
as "not implemented in this execution context", which blamed the proof shape
instead of the claim. Every execution context now runs a written tactic
through one function, and the arm gives the main line's refusal.

```c filename=a_false_transport_in_a_branch_arm_is_refused_as_on_the_main_line.c
void mark_one(int32 a[], int32 n, int32 i, int32 m, int32 c) {
    if (c) {
        a[i] = 1;
    }
}
```

```click
verifying "a_false_transport_in_a_branch_arm_is_refused_as_on_the_main_line.c";

void mark_one(int32 a[], int32 n, int32 i, int32 m, int32 c) {
    requires 0 <= i;
    requires i < n;
    requires 0 <= m;
    requires m < n;
    requires m != i;
    requires n <= 1073741823;
    owns a[0..n];
    ensures a[m] == old(a[m]);
} by {
    mark entry;
    branch then {
        step();
        transport(at(entry, a[m]) == at(entry, a[m]), at(entry, a[m]) == 5);
    } else {
    }
    execute();
    simp();
}
```

```expect
fail: could not make fact transport premises explicit
```
