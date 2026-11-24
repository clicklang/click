# Induction application proves missing descent premises

In the positive branch, the ordinary solver proves the nonnegativity and
strict descent of the predecessor before applying the hypothesis.

```c filename=an_induction_premise_is_named_when_it_is_not_available.c
void unused(void) {}
```

```click
verifying "an_induction_premise_is_named_when_it_is_not_available.c";

function cd(n: int32) -> int32
    decreases n
{
    if n <= 0 { 0 } else { cd(n - 1) }
}

theorem t(n: int32) {
    requires n >= 0;
    ensures cd(n) == 0 by {
        let ih = induct(n);
        if n <= 0 {
            unfold(cd(n));
            normalize() using { n <= 0; };
        } else {
            apply(ih(n - 1));
            unfold(cd(n));
            rewrite(cd(n - 1), 0);
            close();
        }
    }
}
```

```expect
pass
```
