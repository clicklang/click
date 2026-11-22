# An induction premise is named when it is not available

A missing induction premise is spelled with the measure's name.

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
        }
    }
}
```

```expect
fail: found no available fact for premise `to_integer((0 as int32)) <= to_integer(((n - 1) as int32))`
```
