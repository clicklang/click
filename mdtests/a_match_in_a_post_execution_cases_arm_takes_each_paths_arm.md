# A `match` in a post-execution `cases` arm takes each path's arm

A proof `match` written inside an arm of a post-execution `cases` is decided per outcome path, with each path taking the `match` arm its constructor case selects.

```c filename=a_match_in_a_post_execution_cases_arm_takes_each_paths_arm.c
int read(int* p) { return *p; }
```

```click
verifying "a_match_in_a_post_execution_cases_arm_takes_each_paths_arm.c";

spec enum Tri { Zero, One, Other(int) }

resource cell(p: int*) {
    field model: Tri;
    owns p[0..1];
}

int read(int* p) {
    owns c: cell(p);
    ensures result == p[0];
    ensures c.model == old(c.model);
} by {
    execute();
    cases {
        result > 0 => {
            match old(c.model) {
                Tri::Zero => { simp(); },
                Tri::One => { simp(); },
                Tri::Other(value) => { have old(c.model) == Tri::Other(value); },
            }
        }
        result <= 0 => { simp(); }
    }
}
```

```expect
pass
```
