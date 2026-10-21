# instantiate takes an Integer binder at a literal

An `Integer` binder takes an `Integer` argument. A literal is read as a
mathematical integer, the instantiated guard `0 <= 5` holds without facts,
and the instance closes the goal.

```c filename=instantiate_takes_an_integer_binder_at_a_literal.c
void unused(void) {}
```

```click
verifying "instantiate_takes_an_integer_binder_at_a_literal.c";

function sq(z: Integer) -> Integer { z * z }

theorem lit(g: Integer) {
    requires forall (z: Integer) { 0 <= z implies sq(z) <= g };
    ensures sq(5) <= g by {
        instantiate(forall (z: Integer) { 0 <= z implies sq(z) <= g }, 5);
    }
}
```

```expect
pass
```
