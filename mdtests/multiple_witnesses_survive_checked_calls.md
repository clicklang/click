# Multiple recorded pointer witnesses survive repeated calls

Each returned body retains both witness bindings. Their origins come from the
selected body's two words, and consumers reuse that construction.

```c filename=multiple_returned_witnesses.c
struct node { unsigned long left; unsigned long right; };
void keep(struct node* node) {}
void forward(struct node* node) { keep(node); keep(node); }
```

```click
resource packed(node: struct node*) {
    owns *node;
    let left: struct node* where aligned(left, 8) and node->left == address(left) + (node->left & 1);
    let right: struct node* where aligned(right, 8) and node->right == address(right) + (node->right & 1);
}

verifying "multiple_returned_witnesses.c";
void keep(struct node* node) {
    requires node != 0;
    owns packed(node);
}
void forward(struct node* node) {
    requires node != 0;
    owns packed(node);
}
```

```expect
pass
```
