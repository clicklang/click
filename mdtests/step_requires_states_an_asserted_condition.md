# a step's `requires` entry states a checked access's asserted condition

A read of a global array element asserts its index in bounds. When no fact
states that, the step leaves the asserted condition open; a `requires` entry
writes it as the condition itself, which is how expansion spells it, and
proves it at the step's pre-state.

```c filename=step_requires_states_an_asserted_condition.c
int32 values[4];

int32 f(int32 x) {
    int32 r;
    r = values[x];
    return r;
}
```

```click
verifying "step_requires_states_an_asserted_condition.c";

int32 f(int32 x) {
    owns values[0..4];
    requires x == 1 or x == 2;
    ensures result == result;
} by {
    step();
    step() {
        requires x >= 0 and x < 4 by {
            cases {
                x == 1 => { simp(); }
                x == 2 => { simp(); }
            }
        }
    }
    step();
    step();
    simp();
}
```

```expect
pass
```
