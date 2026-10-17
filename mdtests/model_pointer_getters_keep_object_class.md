# A pure getter must preserve its model field’s pointer class

```c filename=getter.c
struct model_node { uint64 word; };
void direct(void) {}
void via_getter(void) {}
void via_nested(void) {}
void via_identity(struct model_node* p) {}
```

```click
verifying "getter.c";
spec enum MaybeRef { Missing, Present(struct model_node*), }
spec enum NodeRef { At(struct model_node*), }
function selected(m: MaybeRef, fallback: struct model_node*) -> struct model_node* {
    match m {
        MaybeRef::Missing => fallback,
        MaybeRef::Present(p) => p,
    }
}
function nested(m: MaybeRef, fallback: struct model_node*) -> struct model_node* {
    selected(m, fallback)
}
function identity(p: struct model_node*) -> struct model_node* { p }
resource source() { field model: MaybeRef; }
resource token() { field model: NodeRef; }

void direct() {
    owns src: source();
    produces held: token();
    ensures true;
} by {
    execute();
    match src.model {
        MaybeRef::Missing => { let held = fold(token(), { model: NodeRef::At(0) }); },
        MaybeRef::Present(p) => { let held = fold(token(), { model: NodeRef::At(p) }); },
    }
}

void via_getter() {
    owns src: source();
    produces held: token();
    ensures true;
} by {
    execute();
    let held = fold(token(), { model: NodeRef::At(selected(src.model, 0)) });
}

void via_nested() {
    owns src: source();
    produces held: token();
    ensures true;
} by {
    execute();
    let held = fold(token(), { model: NodeRef::At(nested(src.model, 0)) });
}
void via_identity(struct model_node* p) {
    produces held: token();
    ensures held.model == NodeRef::At(identity(p));
} by {
    execute();
    let held = fold(token(), { model: NodeRef::At(identity(p)) });
}
```

```expect
pass
```
