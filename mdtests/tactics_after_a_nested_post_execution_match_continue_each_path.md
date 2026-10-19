# Tactics after a nested post-execution `match` continue each path

A `match` nested in a post-execution `if` arm is decided per outcome path, so it does not fork a shared proof state: a tactic written after it in the same arm continues each path after that path's `match` arm. Here the arms establish facts and the trailing `simp()` closes the claims.

```c filename=tactics_after_a_nested_post_execution_match_continue_each_path.c
int read(int* p) { return *p; }
```

```click
verifying "tactics_after_a_nested_post_execution_match_continue_each_path.c";

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
    if (result > 0) {
        match old(c.model) {
            Tri::Zero => { have old(c.model) == Tri::Zero; },
            Tri::One => { have old(c.model) == Tri::One; },
            Tri::Other(value) => { have old(c.model) == Tri::Other(value); },
        }
        simp();
    } else {
        simp();
    }
}
```

```expect
pass
```
