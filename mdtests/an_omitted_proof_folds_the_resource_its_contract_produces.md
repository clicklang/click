# An omitted proof folds the resource its contract produces

The closer an omitted proof stands for folds a resource the contract
produces when a returned path holds that resource's body: the
`fold(owned_node(result))` a script would write after the C runs, on each
path. Here one path returns null, where the resource holds nothing, and the
other returns the initialized node. Expansion prints the fold on each path.

When the fold does not check, the path is left as it was and the claim
reports what is missing
(`mdtests/an_omitted_proof_that_cannot_fold_its_produced_resource_names_it.md`).

```c filename=an_omitted_proof_folds_the_resource_its_contract_produces.c
struct node {
    int32 value;
};

struct node* make_node() {
    struct node* node = malloc(sizeof(struct node));
    if (node == 0) {
        return 0;
    }
    node->value = 0;
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

verifying "an_omitted_proof_folds_the_resource_its_contract_produces.c";

struct node* make_node() {
    produces owned_node(result);
    ensures result != 0 implies result->value == 0;
}
```

```expect
pass
```
