# A model pointer alone does not grant field-read authority to a fold

The resource owns the fields at `p`, but its model pointer is not proved equal
to `p`. A checked fact about `p->left` cannot authorize reading `id->left` as a
fold argument.

```c filename=probe.c
struct Node { unsigned long tag; struct Node *left; };
void put(struct Node *p) { p->tag = 0; }
```

```click
verifying "probe.c";
spec enum Model { At(struct Node*) }
resource node(p: struct Node*) {
 field model: Model;
 match model { Model::At(id) => { owns p->tag; owns p->left; fact p->left == 0; }, }
}
resource empty(p: struct Node*) { field model: int32; fact model == 0; fact p == 0; }
void put(struct Node* p) {
 consumes n: node(p);
 produces p->tag; produces p->left;
 produces e: empty(p->left);
 ensures 1 == 1;
} by {
 match n.model { Model::At(id) => {
  unfold(n); step();
  have p->left == 0;
  let e = fold(empty(id->left), { model: 0 });
  execute(); simp();
 }, }
}
```

```expect
fail: could not lower resource `empty` argument 0
```
