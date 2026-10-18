# `cases` at an execution frontier finishes each arm

At an execution frontier `cases` splits on an available disjunction: each arm receives exactly its own disjunct, here `x == 1`, `x == 2` or `x == 3`. With nothing written after the `cases`, each arm runs the rest of the function and finishes its own path.

```c filename=cases_at_a_frontier_finishes_each_arm.c
int32 f(int32 x) {
    if (x > 0) {
        return 1;
    }
    return 0;
}
```

```click
verifying "cases_at_a_frontier_finishes_each_arm.c";

int32 f(int32 x) {
    requires x == 1 or x == 2 or x == 3;
    ensures result == 1;
} by {
    cases {
        x == 1 => { execute(); }
        x == 2 => { execute(); }
        x == 3 => { execute(); }
    }
}
```

```expect
pass
```
