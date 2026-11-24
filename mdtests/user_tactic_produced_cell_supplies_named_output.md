# Named outputs read a sibling produced cell

A folded input owns the root link in either model case. Applying the checked
tactic exposes that link and its child. The child argument may read the link
returned by the same tactic, regardless of output-clause order.

```c filename=dependent_outputs.c
struct slot { struct slot *next; int32 *p; };
void chained(struct slot *root) {}
void user(struct slot *root) {}
void reversed(struct slot *root) {}
void expose_c(struct slot *root) {}
void call_c(struct slot *root) { expose_c(root); }
```

```click
verifying "dependent_outputs.c";
spec enum Shape { A, B }
resource leaf(p: int32*) { field tag: int32; owns *p; }
resource bundle(root: struct slot*) {
    field shape: Shape;
    field tag: int32;
    match shape {
        Shape::A => { owns root->p; owns child: leaf(root->p); fact child.tag == tag; },
        Shape::B => { owns root->p; owns child: leaf(root->p); fact child.tag == tag; },
    }
}
tactic expose(root: struct slot*) {
    consumes state: bundle(root);
    produces root->p;
    produces out: leaf(root->p);
    ensures defined(root->p);
} by {
    match state.shape {
        Shape::A => { let { child: out } = unfold(state); have defined(root->p) by { close(); } },
        Shape::B => { let { child: out } = unfold(state); have defined(root->p) by { close(); } },
    }
}
void user(struct slot* root) {
    consumes state: bundle(root);
    produces root->p;
    produces out: leaf(root->p);
} by {
    let { out: out } = expose(root, { state: state });
}

tactic expose_reversed(root: struct slot*) {
    consumes state: bundle(root);
    produces out: leaf(root->p);
    produces root->p;
    ensures defined(root->p);
} by {
    match state.shape {
        Shape::A => { let { child: out } = unfold(state); have defined(root->p) by { close(); } },
        Shape::B => { let { child: out } = unfold(state); have defined(root->p) by { close(); } },
    }
}
void reversed(struct slot* root) {
    consumes state: bundle(root);
    produces out: leaf(root->p);
    produces root->p;
} by {
    let { out: out } = expose_reversed(root, { state: state });
}

void expose_c(struct slot* root) {
    consumes state: bundle(root);
    produces out: leaf(root->p);
    produces root->p;
    ensures defined(root->p);
} by {
    match state.shape {
        Shape::A => { let { child: out } = unfold(state); step_until(function.exit); },
        Shape::B => { let { child: out } = unfold(state); step_until(function.exit); },
    }
}
void call_c(struct slot* root) {
    consumes state: bundle(root);
    produces out: leaf(root->p);
    produces root->p;
} by {
    let { out: out } = step(expose_c, { state: state });
}

resource chain_bundle(root: struct slot*) {
    field shape: Shape;
    field tag: int32;
    match shape {
        Shape::A => {
            owns root->next;
            owns root->next->p;
            owns child: leaf(root->next->p);
            fact child.tag == tag;
        },
        Shape::B => {
            owns root->next;
            owns root->next->p;
            owns child: leaf(root->next->p);
            fact child.tag == tag;
        },
    }
}
tactic expose_chain(root: struct slot*) {
    consumes state: chain_bundle(root);
    produces out: leaf(root->next->p);
    produces root->next->p;
    produces root->next;
    ensures defined(root->next);
    ensures defined(root->next->p);
} by {
    match state.shape {
        Shape::A => { let { child: out } = unfold(state); have defined(root->next) by { close(); } have defined(root->next->p) by { close(); } },
        Shape::B => { let { child: out } = unfold(state); have defined(root->next) by { close(); } have defined(root->next->p) by { close(); } },
    }
}
void chained(struct slot* root) {
    consumes state: chain_bundle(root);
    produces out: leaf(root->next->p);
    produces root->next->p;
    produces root->next;
} by {
    let { out: out } = expose_chain(root, { state: state });
}
```

```expect
pass
```
