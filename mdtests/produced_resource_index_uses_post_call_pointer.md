# A produced resource index uses the post-call pointer

The field is overwritten before return. The declared output must name the
replacement cell rather than the old child.

```c filename=produced_resource_index_uses_post_call_pointer.c
struct node { int value; };
struct root { struct node *node; };
void release(struct root *root, struct node *replacement) { root->node = replacement; }
void caller(struct root *root, struct node *replacement) { release(root, replacement); }
```

```click
verifying "produced_resource_index_uses_post_call_pointer.c";
resource cell(p: struct node*) { field tag: int32; owns p->value; }
spec enum Shape { Empty, Node }
resource bundled(root: struct root*) {
    field shape: Shape;
    field tag: int32;
    match shape {
        Shape::Empty => { fact 0 == 1; },
        Shape::Node => {
            owns root->node;
            owns leaf: cell(root->node);
            fact leaf.tag == tag;
        },
    }
}

void release(struct root* root, struct node* replacement) {
    consumes state: bundled(root);
    consumes incoming: cell(replacement);
    produces root->node;
    produces leaf: cell(root->node);
    ensures root->node == replacement;
} by {
    match state.shape {
        Shape::Empty => { unfold(state); contradiction(0 == 1); },
        Shape::Node => {
            let { leaf: original } = unfold(state);
            unfold(incoming);
            step();
            let leaf = fold(cell(root->node), { tag: old(incoming.tag) });
            execute(); simp();
        },
    }
}
void caller(struct root* root, struct node* replacement) {
    consumes state: bundled(root);
    consumes incoming: cell(replacement);
    produces root->node;
    produces leaf: cell(root->node);
    ensures root->node == replacement;
} by {
    let { leaf: leaf } = step(release(root, replacement), { state: state, incoming: incoming });
    execute(); simp();
}
```

```expect
pass
```
