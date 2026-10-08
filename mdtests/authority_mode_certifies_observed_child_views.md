# Contract certification accepts views of observed children in authority mode

`tree_sum` views `tree(node)` and observes the trees of both children before
reading their values. This is reduced from `examples/binary-tree`.

Two certification checks failed under authority semantics:

- The entry check expands the held resources one level. The observations had
  already projected `tree(node->left)` and `tree(node->right)` as views, and
  that expansion replaced them with their bodies, so the required child views
  seemed missing. A view is duplicable, so one the unexpanded entry holds
  satisfies the requirement.
- The proof loads the children's cells, which the entry holds only through
  the folded child trees. Such a viewability premise is now retried against
  the entry's composites opened level by level, as deep as the entry facts
  decide.

```c filename=tree_sum.c
struct node {
    int32 value;
    struct node* left;
    struct node* right;
};

int32 tree_sum(struct node* node) {
    int32 sum;
    sum = node->value + node->left->value;
    return sum + node->right->value;
}
```

```click resource_semantics=authority
resource tree(node: struct node*) {
    if node != 0 {
        owns node->value;
        owns node->left;
        owns node->right;
        owns tree(node->left);
        owns tree(node->right);
    }
}

verifying "tree_sum.c";

int32 tree_sum(struct node* node) {
    requires node != 0;
    requires node->left != 0;
    requires node->right != 0;
    requires 0 <= node->value;
    requires node->value <= 715827882;
    requires 0 <= node->left->value;
    requires node->left->value <= 715827882;
    requires 0 <= node->right->value;
    requires node->right->value <= 715827882;
    views tree(node);

    ensures result == node->value + node->left->value + node->right->value;
} by {
    observe(tree(node));
    observe(tree(node->left));
    observe(tree(node->right));
    step();
    step();
    step();
    have result == ((node->value + node->left->value) + node->right->value) by {
        normalize();
    }
    assumption();
}
```

```expect
pass
```
