# Model pointer fields accept their declared type and null

A model constructor preserves its declared pointer field type. Null remains
a value of that type.

```c filename=model_fields.c
struct model_node { uint64 word; };
void capture(struct model_node* p) {}
void capture_null(void) {}
void capture_known_null(void* p) {}
```

```click
verifying "model_fields.c";
spec enum NodeRef { At(struct model_node*), }
resource token() { field model: NodeRef; }

void capture(struct model_node* p) {
    produces held: token();
    ensures held.model == NodeRef::At(p);
} by {
    execute();
    let held = fold(token(), { model: NodeRef::At(p) });
}

void capture_null() {
    produces held: token();
    ensures true;
} by {
    execute();
    let held = fold(token(), { model: NodeRef::At(0) });
}

void capture_known_null(void* p) {
    requires p == 0;
    produces held: token();
    ensures true;
} by {
    execute();
    let held = fold(token(), { model: NodeRef::At((struct model_node*)p) });
}
```

```expect
pass
```
