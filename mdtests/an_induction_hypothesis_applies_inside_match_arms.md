# An induction hypothesis applies inside match arms

A proof `match` over a parameter the induction does not touch can use `ih`
in each arm, here inside an `else` branch.

```c filename=an_induction_hypothesis_applies_inside_match_arms.c
void unused(void) {}
```

```click
verifying "an_induction_hypothesis_applies_inside_match_arms.c";

spec enum Choice { A, B }

function cd(n: int32) -> int32
    decreases n
{
    if n <= 0 { 0 } else { cd(n - 1) }
}

theorem t(n: int32, c: Choice) {
    requires n >= 0;
    ensures cd(n) == 0 by {
        induct(n) as ih;
        if n <= 0 {
            unfold(cd(n));
            normalize() using { n <= 0; };
        } else {
            match c {
                Choice::A => { apply(ih(n - 1)); unfold(cd(n)); rewrite(cd(n - 1) == 0); normalize(); },
                Choice::B => { apply(ih(n - 1)); unfold(cd(n)); rewrite(cd(n - 1) == 0); normalize(); },
            }
        }
    }
}
```

```expect
pass
```
