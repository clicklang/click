# An unknown C pointer cannot establish a model field's nominal class

```c filename=call.c
struct model_node { uint64 word; };
void wrapped(struct model_node* p) {}
void caller(void* p) { wrapped((struct model_node*)p); }
```

```click
verifying "call.c";
spec enum NodeRef { At(struct model_node*), }
resource token() { field model: NodeRef; }
void wrapped(struct model_node* p) { produces held: token(); ensures held.model == NodeRef::At(p); } by {
    execute(); let held = fold(token(), { model: NodeRef::At(p) });
}
void caller(void* p) { produces held: token(); ensures true; } by {
    let { held: held } = step(wrapped((struct model_node*)p), {}); execute();
}
```

```expect
fail: requires original object class `struct model_node` or null
```
