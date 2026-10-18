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
} by {
    match state.shape {
        Shape::A => { let { child: out } = unfold(state); },
        Shape::B => { let { child: out } = unfold(state); },
    }
}
void user(struct slot* root) {
    consumes state: bundle(root);
    produces root->p;
    produces out: leaf(root->p);
} by {
    let { out: out } = expose(root, { state: state });
    execute();
}

tactic expose_reversed(root: struct slot*) {
    consumes state: bundle(root);
    produces out: leaf(root->p);
    produces root->p;
} by {
    match state.shape {
        Shape::A => { let { child: out } = unfold(state); },
        Shape::B => { let { child: out } = unfold(state); },
    }
}
void reversed(struct slot* root) {
    consumes state: bundle(root);
    produces out: leaf(root->p);
    produces root->p;
} by {
    let { out: out } = expose_reversed(root, { state: state });
    execute();
}

void expose_c(struct slot* root) {
    consumes state: bundle(root);
    produces out: leaf(root->p);
    produces root->p;
} by {
    match state.shape {
        Shape::A => { let { child: out } = unfold(state); execute(); },
        Shape::B => { let { child: out } = unfold(state); execute(); },
    }
}
void call_c(struct slot* root) {
    consumes state: bundle(root);
    produces out: leaf(root->p);
    produces root->p;
} by {
    let { out: out } = step(expose_c(root), { state: state });
    execute();
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
} by {
    match state.shape {
        Shape::A => { let { child: out } = unfold(state); },
        Shape::B => { let { child: out } = unfold(state); },
    }
}
void chained(struct slot* root) {
    consumes state: chain_bundle(root);
    produces out: leaf(root->next->p);
    produces root->next->p;
    produces root->next;
} by {
    let { out: out } = expose_chain(root, { state: state });
    execute();
}
```

```expect
pass
```
