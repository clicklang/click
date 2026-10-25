# An omitted proof that cannot fold its produced resource names it

The closer an omitted proof stands for tries to fold a resource the
contract produces. Here the returned node was never allocated, so
`owned_node(result)` does not fold; the path is left as it was, and the
claim reports the resource it is missing.

```c filename=an_omitted_proof_that_cannot_fold_its_produced_resource_names_it.c
struct node {
    int32 value;
};

struct node* pass_node(struct node* node) {
    return node;
}
```

```click
resource owned_node(node: struct node*) {
    if node != 0 {
        owns allocation(node, sizeof(struct node));
        owns *node;
    }
}

verifying "an_omitted_proof_that_cannot_fold_its_produced_resource_names_it.c";

struct node* pass_node(struct node* node) {
    requires node != 0;
    produces owned_node(result);
}
```

```expect
fail: left `pass_node.produces_0` unproved
```
