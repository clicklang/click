# Each proof `if` arm may reuse a `match` binding name

A proof `match` whose arms reach function exit keeps its field bindings on
those finished paths, so tactics written after the `match` in the same arm
can name them. They do not reach the other arm of an enclosing proof `if`:
that arm starts in the scope the `if` was written in, so its own `match`
may bind `v` again.

```c filename=each_proof_if_arm_may_reuse_a_match_binding_name.c
int read(int* p) { return *p; }
```

```click
verifying "each_proof_if_arm_may_reuse_a_match_binding_name.c";

spec enum Tri { Zero, One, Other(int) }

resource cell(p: int*) {
    field model: Tri;
    owns p[0..1];
}

int read(int* p) {
    owns c: cell(p);
    ensures result == p[0];
} by {
    if (p[0] > 0) {
        match c.model {
            Tri::Zero => { execute(); simp(); },
            Tri::One => { execute(); simp(); },
            Tri::Other(v) => { execute(); simp(); },
        }
    } else {
        match c.model {
            Tri::Zero => { execute(); simp(); },
            Tri::One => { execute(); simp(); },
            Tri::Other(v) => { execute(); simp(); },
        }
    }
}
```

```expect
pass
```
