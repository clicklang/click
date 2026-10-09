# Fold arguments read owned fields through proved model-pointer aliases

After the tag write, the unchanged child field is readable through the model
binding `id`, as the `have` demonstrates. A named fold must retain that same
checked alias and read authority when evaluating its resource argument.

```c filename=probe.c
struct Node { unsigned long tag; struct Node *left; };
void put(struct Node *p) { p->tag = 0; }
```

```click
verifying "probe.c";
spec enum Model { At(struct Node*) }
resource node(p: struct Node*) {
 field model: Model;
 match model { Model::At(id) => { owns p->tag; owns p->left; fact p == id; fact p->left == 0; }, }
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
  have id->left == 0 by { simp(); }
  let e = fold(empty(id->left), { model: 0 });
  execute(); simp();
 }, }
}
```

```expect
pass
```
