# A `match` after execution finishes each arm

After execution a proof `match` splits the outcome paths into one path per live constructor arm, and with nothing written after it each arm finishes its own path. The `Other` arm proves a fact about its own field binding before the implicit `auto` closes its claims.

```c filename=match_after_execution_finishes_each_arm.c
int read(int* p) { return *p; }
```

```click
verifying "match_after_execution_finishes_each_arm.c";

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
    match old(c.model) {
        Tri::Zero => { simp(); },
        Tri::One => { simp(); },
        Tri::Other(value) => { have old(c.model) == Tri::Other(value); },
    }
}
```

```expect
pass
```
