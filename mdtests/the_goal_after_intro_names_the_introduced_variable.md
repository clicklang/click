# The goal after intro names the introduced variable

After `intro()`, the remaining goal spells the introduced variable by the name
the quantifier gave it, and the binder still bound in the goal keeps its own
written name.

```c filename=the_goal_after_intro_names_the_introduced_variable.c
void unused(void) {}
```

```click
verifying "the_goal_after_intro_names_the_introduced_variable.c";

theorem t(n: int32) {
    ensures forall (a: int32) { forall (b: int32) { a == b } } by {
        intro();
        normalize();
    }
}
```

```expect
fail: goal: forall (b: int32) { a == b }
```
