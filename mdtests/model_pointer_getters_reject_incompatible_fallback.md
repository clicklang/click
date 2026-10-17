# A getter checks the actual fallback's object class

```c filename=getter.c
struct model_node { uint64 word; };
struct other_node { uint64 word; };
void wrong(struct other_node* p) {}
```

```click
verifying "getter.c";
spec enum MaybeRef { Missing, Present(struct model_node*), }
spec enum NodeRef { At(struct model_node*), }
function selected(m: MaybeRef, fallback: struct model_node*) -> struct model_node* {
    match m { MaybeRef::Missing => fallback, MaybeRef::Present(p) => p, }
}
resource source() { field model: MaybeRef; }
resource token() { field model: NodeRef; }
void wrong(struct other_node* p) {
    owns src: source();
    produces held: token();
    ensures true;
} by {
    execute();
    let held = fold(token(), {
        model: NodeRef::At(selected(src.model, (struct model_node*)(void*)p))
    });
}
```

```expect
fail: algebraic initializer must denote one symbolic value
```
