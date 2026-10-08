# A restored loop frame remains separate from reconstructed ownership
```c filename=walk.c
struct Node { struct Node *next; };
void walk(struct Node *p, int *marker) {
    struct Node *q = p;
    do { p = p->next; break; } while (p);
    q->next = 0;
}
```
```click
verifying "walk.c";
spec enum Chain { Empty, Node(struct Node*, Chain), }
spec enum Path { Top, Step(struct Node*, Path), }
resource list(p: struct Node*) {
    field model: Chain;
    match model {
        Chain::Empty => { fact p == 0; },
        Chain::Node(identity, rest) => {
            owns p->next;
            owns tail: list(p->next);
            fact p != 0;
            fact p == identity;
            fact tail.model == rest;
        },
    }
}
resource path(p: struct Node*) {
    field model: Path;
    match model {
        Path::Top => { },
        Path::Step(identity, before) => {
            owns identity->next;
            owns up: path(identity);
            fact identity != 0;
            fact identity->next == p;
            fact up.model == before;
        },
    }
}
void walk(struct Node* p, int32* marker) {
    consumes t: list(p);
    owns marker[0];
    requires p != 0;
    requires marker[0] == 9;
    ensures marker[0] == 9;
} by {
    step(); step();
    let c = fold(path(p), { model: Path::Top });
    loop {
        owns t: list(p);
        owns c: path(p);
        decreases t;
        invariant p != 0;
        invariant p == q;
        initialize by simp;
        preserve by {
            match t.model {
                Chain::Empty => { unfold(t); contradiction(p == 0); },
                Chain::Node(identity, rest) => {
                    let { tail: next } = unfold(t);
                    let frame = fold(path(p->next), { model: Path::Step(identity, c.model) }, { up: c });
                    step();
                    step();
                },
            }
        }
    }
    have c.model != Path::Top by normalize();
    match c.model {
        Path::Top => { contradiction(c.model == Path::Top); },
        Path::Step(identity, before) => {
            let { up: previous } = unfold(c);
            execute(); simp();
        },
    }
}
```
```expect
pass
```
