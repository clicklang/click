# A model match can establish a shared interface after return

The constructor assumptions stay in their arms. The continuation receives
the interface fact and held resource, then closes the remaining contract obligations once.

```c filename=match_after_execution_that_would_fork_is_refused.c
int read(int* p) { return *p; }
```

```click
verifying "match_after_execution_that_would_fork_is_refused.c";

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
    step_until(function.exit);
    match old(c.model) ensuring { owns c: cell(p); fact result == p[0]; } {
        Tri::Zero => { have old(c.model) == Tri::Zero; },
        Tri::One => { have old(c.model) == Tri::One; },
        Tri::Other(value) => { have old(c.model) == Tri::Other(value); },
    }
    close();
}
```

```expect
pass
```
