# A C wrapper propagates the object-type premise used by its callee

```c filename=call.c
struct model_node { uint64 word; };
void wrapped(struct model_node* p) {}
void forward(struct model_node* p) { wrapped(p); }
void caller(void* p) { forward((struct model_node*)p); }
```

```click
verifying "call.c";
spec enum NodeRef { At(struct model_node*), }
resource token() { field model: NodeRef; }
void wrapped(struct model_node* p) { produces held: token(); ensures held.model == NodeRef::At(p); } by {
    step_until(function.exit); let held = fold(token(), { model: NodeRef::At(p) });
}
void forward(struct model_node* p) { produces held: token(); ensures held.model == NodeRef::At(p); } by {
    let { held: held } = step(wrapped, {});
}
void caller(void* p) { produces held: token(); ensures true; } by {
    let { held: held } = step(forward, {});
}
```

```expect
fail: requires original object class `struct model_node` or null
```
