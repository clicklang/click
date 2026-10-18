# `cases` after execution requires its disjunction

A `cases` after execution forks an outcome path only where its disjunction is an exact available fact on that path. Here the contract gives `x == 1 or x == 3`, not the written `x == 1 or x == 2`, so the split is refused, naming the disjunction.

```c filename=cases_after_execution_requires_its_disjunction.c
int32 f(int32 x) {
    return x;
}
```

```click
verifying "cases_after_execution_requires_its_disjunction.c";

int32 f(int32 x) {
    requires x == 1 or x == 3;
    ensures result >= 1;
} by {
    execute();
    cases {
        x == 1 => { simp(); }
        x == 2 => { simp(); }
    }
}
```

```expect
fail: `cases` after execution requires its exact disjunction as an available fact on each outcome path: `x == 1 or x == 2`
```
