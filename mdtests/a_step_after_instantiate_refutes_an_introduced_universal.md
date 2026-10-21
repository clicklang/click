# A step after instantiate refutes an introduced universal

`intro()` of `not (forall ...)` leaves the goal `false` with the universal as
a fact. `instantiate` at the counterexample `1` gives `1 == 0`, and the
following `contradiction` closes the goal, as it does when the universal is a
requirement.

```c filename=a_step_after_instantiate_refutes_an_introduced_universal.c
void unused(void) {}
```

```click
verifying "a_step_after_instantiate_refutes_an_introduced_universal.c";

theorem not_all_zero(n: int32) {
    ensures not (forall (x: int32) { x == 0 }) by {
        intro();
        instantiate(forall (x: int32) { x == 0 }, 1);
        contradiction(1 == 0);
    }
}
```

```expect
pass
```
