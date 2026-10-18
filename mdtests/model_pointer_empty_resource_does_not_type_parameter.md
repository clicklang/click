# An address-only resource does not confer nominal parameter typing

Opening an empty resource has no typed logical call requirement to recover.

```c filename=resource_type.c
struct node { uint64 word; };
void keep(struct node* p) {}
```

```click
verifying "resource_type.c";
spec enum Ref { At(struct node*), }
function valid(p: struct node*) -> int32 { 1 }
resource token(p: struct node*) { field model: int; }
resource output() { field model: Ref; }
void keep(struct node* p) {
    produces out: output();
    owns held: token(p);
    ensures held.model == old(held.model);
} by {
    unfold(held);
    execute();
    let out = fold(output(), { model: Ref::At(p) });
}
```

```expect
fail: algebraic initializer must denote one symbolic value
```
