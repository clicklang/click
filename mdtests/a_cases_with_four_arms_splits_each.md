# A `cases` with four arms splits each

`cases` over `A or B or C or D` splits as nested two-way splits, the last arm
against the disjunction of the earlier ones. Each inner split is numbered
from the written tactic's position and its own arm count. Numbering an inner
split from the split around it instead overflowed at the third level, so a
`cases` with four or more arms stopped the verifier.

```c filename=a_cases_with_four_arms_splits_each.c
int f(int x)
{
	return x;
}
```

```click
verifying "a_cases_with_four_arms_splits_each.c";

int32 f(int32 x) {
    requires x == 0 or x == 1 or x == 2 or x == 3;
    ensures result <= 3;
} by {
    cases {
        x == 0 => { execute(); simp(); }
        x == 1 => { execute(); simp(); }
        x == 2 => { execute(); simp(); }
        x == 3 => { execute(); simp(); }
    }
}
```

```expect
pass
```
