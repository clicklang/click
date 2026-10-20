# A pure match runs inside an if arm

A proof `match` in a pure theorem rejoins when it is nested in the `else`
arm of a proof `if`, after the `then` arm has closed its own branch.

```c filename=a_pure_match_runs_inside_an_if_arm.c
void unused(void) {}
```

```click
verifying "a_pure_match_runs_inside_an_if_arm.c";

spec enum Choice { A, B }

theorem t(n: int32, c: Choice) {
    requires n >= 1;
    ensures n >= 0 by {
        if n <= 5 {
            arithmetic() using { n >= 1; };
        } else {
            match c {
                Choice::A => { arithmetic() using { n >= 1; }; },
                Choice::B => { arithmetic() using { n >= 1; }; },
            }
        }
    }
}
```

```expect
pass
```
