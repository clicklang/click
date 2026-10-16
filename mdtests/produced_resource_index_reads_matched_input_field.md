# A produced resource index reads a matched input field

The call argument frame must use the same decided-arm authority as ordinary
return clauses. The impossible empty arm does not hide the root field.

```c filename=produced_resource_index_reads_matched_input_field.c
struct node { int value; };
struct root { struct node *node; };
void release(struct root *root) {}
void caller(struct root *root) { release(root); }
```

```click
verifying "produced_resource_index_reads_matched_input_field.c";
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
    produces root->node;
    produces leaf: cell(root->node);
} by {
    match state.shape {
        Shape::Empty => { unfold(state); contradiction(0 == 1); },
        Shape::Node => { let { leaf: leaf } = unfold(state); execute(); },
    }
}
void caller(struct root* root) {
    consumes state: bundled(root);
    produces root->node;
    produces leaf: cell(root->node);
} by {
    let { leaf: leaf } = step(release(root), { state: state });
    execute();
}
```

```expect
pass
```
