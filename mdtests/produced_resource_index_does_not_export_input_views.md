# Argument evaluation does not export a consumed field view

The input field can locate the returned child without becoming caller-owned
or caller-readable when the callee does not return that field.

```c filename=produced_resource_index_does_not_export_input_views.c
struct node { int value; };
struct root { struct node *node; };
void release(struct root *root) {}
struct node *caller(struct root *root) { release(root); return root->node; }
```

```click
verifying "produced_resource_index_does_not_export_input_views.c";
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

void release(struct root* root) {
    consumes state: bundled(root);
    produces leaf: cell(root->node);
} by {
    match state.shape {
        Shape::Empty => { unfold(state); contradiction(0 == 1); },
        Shape::Node => { let { leaf: leaf } = unfold(state); execute(); },
    }
}
struct node* caller(struct root* root) {
    consumes state: bundled(root);
} by {
    let { leaf: leaf } = step(release(root), { state: state });
    execute();
}
```

```expect
fail: access outside the subobject the pointer designates
```
