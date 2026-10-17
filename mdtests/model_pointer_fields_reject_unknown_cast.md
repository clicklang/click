# A cast cannot manufacture a model field’s original object class

A `void*` value has no retained object class. Casting it to the field’s
pointer spelling does not establish the model’s nominal class guarantee.

```c filename=model_fields.c
struct model_node { uint64 word; };
void unknown(void* p) {}
```

```click
verifying "model_fields.c";
spec enum NodeRef { At(struct model_node*), }
resource token() { field model: NodeRef; }

void unknown(void* p) {
    produces held: token();
    ensures true;
} by {
    execute();
    let held = fold(token(), { model: NodeRef::At((struct model_node*)p) });
}
```

```expect
fail: algebraic initializer must denote one symbolic value
```
