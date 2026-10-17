# A proof cannot add an object-type precondition absent from its declaration

The declared output has an abstract model. Choosing a model that mentions the
input pointer in the proof does not add a requirement to the public contract.

```c filename=body_type.c
struct model_node { uint64 word; };
void hidden_requirement(struct model_node* p) {}
```

```click
verifying "body_type.c";
spec enum Ref { At(struct model_node*), }
resource token() { field model: Ref; }
void hidden_requirement(struct model_node* p) {
    produces held: token();
    ensures true;
} by {
    execute();
    let held = fold(token(), { model: Ref::At(p) });
}
```

```expect
fail: algebraic initializer must denote one symbolic value
```
