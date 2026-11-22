# A folded composite supplies a dependent composite argument

The first `pair(node)` clause owns `node`'s `left` link and the `left` link
of `node`'s left child.  The second clause must load `node->left->left` to form its
argument; its access comes from the folded body of the first composite.
The third clause follows another two links, using the second composite
without claiming either of its cells again. Both contracts exercise the
same dependency chain.

```c filename=dependent_pair.c
struct node {
    struct node *left;
    int32 value;
};

void probe(struct node *node) { }
```

```click
resource pair(node: struct node*) {
    owns node->left;
    owns node->left->left;
}

verifying "dependent_pair.c";

void probe(struct node* node) {
    requires node != 0;
    requires node->left != 0;
    owns pair(node);
    owns pair(node->left->left);
    owns pair(node->left->left->left->left);
}

contract void DependentPair(struct node* node) {
    requires node != 0;
    requires node->left != 0;
    owns pair(node);
    owns pair(node->left->left);
    owns pair(node->left->left->left->left);
}
```

```expect
pass
```
