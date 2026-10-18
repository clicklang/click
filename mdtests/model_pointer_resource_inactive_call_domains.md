# An inactive resource body supplies no logical call type evidence

```c filename=inactive_type.c
struct node { uint64 word; };
void keep(struct node* p) {}
```

```click
verifying "inactive_type.c";
spec enum Ref { At(struct node*), }
function valid(p: struct node*) -> int32 { 1 }
resource token(p: struct node*, enabled: int32) {
    field model: int;
    if enabled != 0 { fact valid(p) == 1; }
}
resource output() { field model: Ref; }
void keep(struct node* p) {
    produces out: output();
    owns held: token(p, 0);
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
