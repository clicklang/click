# An induction hypothesis applies inside a have

The hypothesis `ih` from scalar `induct` is in scope for the rest of the
script, including a `have` proof nested in an `else` branch, written bare or as a
block. The block form with `using` cites the same premises it needs at top
level.

```c filename=an_induction_hypothesis_applies_inside_a_have.c
void unused(void) {}
```

```click
verifying "an_induction_hypothesis_applies_inside_a_have.c";

function cd(n: int32) -> int32
    decreases n
{
    if n <= 0 { 0 } else { cd(n - 1) }
}

theorem block_have(n: int32) {
    requires n >= 0;
    ensures cd(n) == 0 by {
        induct(n) as ih;
        if n <= 0 {
            unfold(cd(n));
            normalize() using { n <= 0; };
        } else {
            have 0 <= n - 1 by auto();
            have n - 1 < n by auto();
            have cd(n - 1) == 0 by { apply(ih(n - 1)) using { 0 <= n - 1; n - 1 < n; }; }
            unfold(cd(n));
            rewrite(cd(n - 1) == 0);
            normalize();
        }
    }
}

theorem bare_have(n: int32) {
    requires n >= 0;
    ensures cd(n) == 0 by {
        induct(n) as ih;
        if n <= 0 {
            unfold(cd(n));
            normalize() using { n <= 0; };
        } else {
            have cd(n - 1) == 0 by apply(ih(n - 1));
            unfold(cd(n));
            rewrite(cd(n - 1) == 0);
            normalize();
        }
    }
}
```

```expect
pass
```
