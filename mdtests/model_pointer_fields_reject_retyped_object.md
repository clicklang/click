# A cast cannot replace a model field’s original object class

The two struct pointers share the kernel pointer carrier. Casting through
`void*` preserves the original class and cannot satisfy the other field type.

```c filename=model_fields.c
struct model_node { uint64 word; };
struct other_node { uint64 word; };
void wrong(struct other_node* p) {}
```

```click
verifying "model_fields.c";
spec enum NodeRef { At(struct model_node*), }
resource token() { field model: NodeRef; }

void wrong(struct other_node* p) {
    produces held: token();
    ensures true;
} by {
    execute();
    let held = fold(token(), { model: NodeRef::At((struct model_node*)(void*)p) });
}
```

```expect
fail: algebraic initializer must denote one symbolic value
```
