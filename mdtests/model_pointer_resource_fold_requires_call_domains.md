# Folding must establish the logical call domain

A C pointer declaration supplies access typing, not checked original-object
evidence. Folding may not borrow the type that the proposed resource promises.

```c filename=resource_type.c
struct node { uint64 word; };
void keep(struct node* p) {}
```

```click
verifying "resource_type.c";
spec enum Ref { At(struct node*), }
function valid(p: struct node*) -> int32 { 1 }
resource token(p: struct node*) {
    field model: int;
    fact valid(p) == 1;
}
void keep(struct node* p) {
    produces held: token(p);
    ensures true;
} by {
    execute();
    let held = fold(token(p), { model: 0 });
}
```

```expect
fail: instance body fact needs an unsupported conditional proof
```
