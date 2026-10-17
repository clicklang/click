# A checked C return retains evidence from an actual declared object

```c filename=global.c
struct model_node { uint64 word; };
static struct model_node singleton = { 0 };
struct model_node* get_node() { return &singleton; }
void wrapped(struct model_node* p) {}
void caller() {
    struct model_node* p = get_node();
    wrapped(p);
}
```

```click
verifying "global.c";
spec enum NodeRef { At(struct model_node*), }
resource token() { field model: NodeRef; }
struct model_node* get_node() { ensures result == &singleton; } by {
    execute(); normalize();
}
void wrapped(struct model_node* p) { produces held: token(); ensures held.model == NodeRef::At(p); } by {
    execute(); let held = fold(token(), { model: NodeRef::At(p) });
}
void caller() { produces held: token(); ensures true; } by {
    step(); step(); let { held: held } = step(wrapped(p), {}); execute();
}
```

```expect
pass
```
