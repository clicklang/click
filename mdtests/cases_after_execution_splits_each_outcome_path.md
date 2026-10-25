# `cases` after execution splits each outcome path

After execution `cases` is a case split on each outcome path, as a proof `if` is: where no disjunct is decided, the path forks into one path per arm, and each arm receives exactly its own disjunct. Here the one outcome path forks three ways and `simp()` closes the claim in each arm.

```c filename=cases_after_execution_splits_each_outcome_path.c
int32 f(int32 x) {
    return x;
}
```

```click
verifying "cases_after_execution_splits_each_outcome_path.c";

int32 f(int32 x) {
    requires x == 1 or x == 2 or x == 3;
    ensures result >= 1;
} by {
    step_until(function.exit);
    cases {
        x == 1 => { solve(); }
        x == 2 => { solve(); }
        x == 3 => { solve(); }
    }
}
```

```expect
pass
```
