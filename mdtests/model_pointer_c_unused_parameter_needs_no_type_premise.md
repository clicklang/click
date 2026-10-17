# An unused C pointer parameter adds no positive object-type premise

```c filename=unused.c
struct model_node { uint64 word; };
void wrapped(struct model_node* p, struct model_node* ignored) {}
void caller(struct model_node* p, void* ignored) { wrapped(p, (struct model_node*)ignored); }
```

```click
verifying "unused.c";
spec enum NodeRef { At(struct model_node*), }
resource token() { field model: NodeRef; }
void wrapped(struct model_node* p, struct model_node* ignored) {
    produces held: token(); ensures held.model == NodeRef::At(p);
} by {
    execute(); let held = fold(token(), { model: NodeRef::At(p) });
}
void caller(struct model_node* p, void* ignored) {
    produces held: token(); ensures held.model == NodeRef::At(p);
} by {
    let { held: held } = step(wrapped(p, (struct model_node*)ignored), {}); execute();
}
```

```expect
pass
```
