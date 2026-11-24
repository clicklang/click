# An induction hypothesis applies inside a have

The hypothesis `ih` from scalar `induct` is in scope for the rest of the
script, including a `have` proof nested in an `else` branch, written bare or as a
block. The same premises are available inside the block.

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
        let ih = induct(n);
        if n <= 0 {
            unfold(cd(n));
            close() using { n <= 0; };
        } else {
            have 0 <= to_integer(n - 1);
            have to_integer(n - 1) < to_integer(n);
            have cd(n - 1) == 0 by { apply(ih(n - 1)); }
            unfold(cd(n));
            rewrite(cd(n - 1), 0);
            known();
        }
    }
}

theorem bare_have(n: int32) {
    requires n >= 0;
    ensures cd(n) == 0 by {
        let ih = induct(n);
        if n <= 0 {
            unfold(cd(n));
            close() using { n <= 0; };
        } else {
            have 0 <= to_integer(n - 1);
            have to_integer(n - 1) < to_integer(n);
            have cd(n - 1) == 0 by apply(ih(n - 1));
            unfold(cd(n));
            rewrite(cd(n - 1), 0);
            known();
        }
    }
}
```

```expect
pass
```
