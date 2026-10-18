# Opening a resource recovers its checked logical call domains

The parameter starts with C access typing only. The selected resource body
promises a well-formed call of `valid`, so opening it recovers the nominal type
needed by `Ref::At(p)`. A C step does not erase that logical requirement.

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
    owns held: token(p);
    ensures held.model == old(held.model);
} by {
    unfold(held);
    step();
    have Ref::At(p) == Ref::At(p) by { simp(); }
    let held = fold(token(p), { model: old(held.model) });
    execute(); simp();
}
```

```expect
pass
```
