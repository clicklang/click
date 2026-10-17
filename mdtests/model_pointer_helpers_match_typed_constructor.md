# Matching a typed pointer constructor retains its field type

```c filename=match.c
struct node { int32 value; };
```

```click
verifying "match.c";
spec enum Ref { At(struct node*), }
function tag(m: Ref) -> int32 { match m { Ref::At(p) => 1, } }
function get(m: Ref) -> struct node* { match m { Ref::At(p) => p, } }
function copy(m: Ref) -> Ref { match m { Ref::At(p) => Ref::At(p), } }

theorem scalar_case(p: struct node*) {
    ensures tag(Ref::At(p)) == 1 by { unfold(tag(Ref::At(p))); normalize(); }
}
theorem pointer_case(p: struct node*) {
    ensures get(Ref::At(p)) == p by { unfold(get(Ref::At(p))); normalize(); }
}
theorem model_case(p: struct node*) {
    ensures copy(Ref::At(p)) == Ref::At(p) by { unfold(copy(Ref::At(p))); normalize(); }
}
```

```expect
pass
```
