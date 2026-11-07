# `cases` at an execution frontier requires its disjunction

The known fact `x == 1` proves that `x == 1 or x == 2` is exhaustive.
The ordinary obligation introduces that disjunction before the exact split.

```c filename=cases_at_a_frontier_requires_its_disjunction.c
int32 f(int32 x) {
    if (x > 0) {
        return 1;
    }
    return 0;
}
```

```click
verifying "cases_at_a_frontier_requires_its_disjunction.c";

int32 f(int32 x) {
    requires x == 1;
    ensures result == 1;
} by {
    cases {
        x == 1 => { }
        x == 2 => { }
    }
}
```

```expect
pass
```
