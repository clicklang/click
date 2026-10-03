# A fact about a `const` pointer parameter is lost after a C step

This is a pinned bug, not intended behaviour; see
`bugs/const-pointer-parameter-fact-is-lost-after-a-step.md`.

`peek` takes `const struct node* p`. Unfolding `x` publishes the body fact
`same(p, p) == 1`. Before any C step, `have same(p, p) == 1 by { assumption(); }`
finds it. After one step, the same `have` does not: the goal written as
`same(p, p) == 1` no longer matches the published fact. Without `const` on the
parameter the proof verifies.

```c filename=const_parameter_fact.c
struct node { int32 shade; };

int32 peek(const struct node* p) {
    int32 seen = 0;
    return 0;
}
```

```click
verifying "const_parameter_fact.c";

function same(a: struct node*, b: struct node*) -> int32 {
    if a == b { 1 } else { 0 }
}

resource here(p: struct node*) {
    field tag: int;
    owns p->shade;
    fact same(p, p) == 1;
}

int32 peek(const struct node* p) {
    owns x: here(p);
    ensures result == 0;
} by {
    unfold(x);
    step();
    have same(p, p) == 1 by { assumption(); }
    let x = fold(here(p), { tag: 0 });
    step();
    step();
    simp();
}
```

```expect
fail: `assumption` requires the current goal as an available semantic fact
```
