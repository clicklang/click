# `cases` at an execution frontier requires its disjunction

The arms of `cases` are only exhaustive when their disjunction holds, so it must be an exact available fact. Here only `x == 1` is known, and the split is refused, naming the disjunction.

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
        x == 1 => { execute(); }
        x == 2 => { execute(); }
    }
}
```

```expect
fail: `cases` requires its exact disjunction as an available fact: `x == 1 or x == 2`
```
