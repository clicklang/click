# A checked model helper cannot receive an incompatible object pointer

```c filename=helper.c
struct model_node { uint64 word; };
struct other_node { uint64 word; };
void wrong(struct other_node* p) {}
```

```click
verifying "helper.c";
spec enum NodeRef { At(struct model_node*), }
function wrapped(p: struct model_node*) -> NodeRef { NodeRef::At(p) }
resource token() { field model: NodeRef; }
void wrong(struct other_node* p) {
    produces held: token();
    ensures true;
} by {
    execute();
    let held = fold(token(), { model: wrapped((struct model_node*)(void*)p) });
}
```

```expect
fail: algebraic initializer must denote one symbolic value
```
