# A bound variable is renamed where its name would capture

A binder prints under its written name unless that name already spells another
variable in the printed goal. Here the inner binder is written `n`, the name of
the theorem's parameter, so it prints with a fresh name instead, and the goal
cannot be misread as being about the parameter.

```c filename=a_bound_variable_is_renamed_where_its_name_would_capture.c
void unused(void) {}
```

```click
verifying "a_bound_variable_is_renamed_where_its_name_would_capture.c";

theorem t(n: int32) {
    ensures forall (a: int32) { forall (n: int32) { a == n } } by {
        intro();
        normalize();
    }
}
```

```expect
fail: goal: forall (k: int32) { a == k }
```
