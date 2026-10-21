# An induction hypothesis applies in a have and a match nested either way

`ih` resolves in a `match` inside a `have` proof and in a `have` inside a
`match` arm.

```c filename=an_induction_hypothesis_applies_in_a_have_and_a_match_nested_either_way.c
void unused(void) {}
```

```click
verifying "an_induction_hypothesis_applies_in_a_have_and_a_match_nested_either_way.c";

spec enum Choice { A, B }

function cd(n: int32) -> int32
    decreases n
{
    if n <= 0 { 0 } else { cd(n - 1) }
}

theorem match_in_have(n: int32, c: Choice) {
    requires n >= 0;
    ensures cd(n) == 0 by {
        induct(n) as ih;
        if n <= 0 {
            unfold(cd(n));
            normalize() using { n <= 0; };
        } else {
            have cd(n - 1) == 0 by {
                match c {
                    Choice::A => { apply(ih(n - 1)); },
                    Choice::B => { apply(ih(n - 1)); },
                }
            }
            unfold(cd(n));
            rewrite(cd(n - 1) == 0);
            normalize();
        }
    }
}

theorem have_in_match(n: int32, c: Choice) {
    requires n >= 0;
    ensures cd(n) == 0 by {
        induct(n) as ih;
        if n <= 0 {
            unfold(cd(n));
            normalize() using { n <= 0; };
        } else {
            match c {
                Choice::A => { have cd(n - 1) == 0 by apply(ih(n - 1)); unfold(cd(n)); rewrite(cd(n - 1) == 0); normalize(); },
                Choice::B => { have cd(n - 1) == 0 by apply(ih(n - 1)); unfold(cd(n)); rewrite(cd(n - 1) == 0); normalize(); },
            }
        }
    }
}
```

```expect
pass
```
