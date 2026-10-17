# Recursive calls retain precisely the input types they use

```c filename=recursive.c
struct model_node { uint64 word; };
void recursive(struct model_node* p, void* q, int32 n) {
    if (n > 0) recursive(p, q, n - 1);
}
```

```click
verifying "recursive.c";
spec enum NodeRef { At(struct model_node*), }
resource token() { field model: NodeRef; }
void recursive(struct model_node* p, void* q, int32 n) {
    requires n >= 0;
    decreases n;
    produces held: token();
    ensures held.model == NodeRef::At(p);
} by {
    if n > 0 {
        step();
        let { held: held } = step(recursive(p, q, n - 1), {});
        execute();
    } else {
        execute();
        let held = fold(token(), { model: NodeRef::At(p) });
    }
}
```

```expect
pass
```
