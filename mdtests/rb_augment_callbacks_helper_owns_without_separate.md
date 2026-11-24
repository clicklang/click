# Owned callback footprints are separate from the borrowed callback table

This is `rb_augment_callbacks_helper_owns.md` without its explicit separation
requirement. The opened table carries checked borrowed projections, while the
helper owns the node links passed to each callback. The validated composition
separates those footprints, preserving subsequent callback reads across the
owned calls. No extra separation premise is needed.

```c filename=rb_augment_callbacks.c
struct node {
    struct node *left;
    struct node *right;
};

struct rb_augment_callbacks {
    void (*propagate)(struct node *node, struct node *stop);
    void (*copy)(struct node *old, struct node *new);
    void (*rotate)(struct node *old, struct node *new);
};

void dummy_propagate(struct node *node, struct node *stop) { }

void dummy_copy(struct node *old, struct node *new) { }

void dummy_rotate(struct node *old, struct node *new) { }

static const struct rb_augment_callbacks dummy_callbacks = {
    .propagate = dummy_propagate,
    .copy = dummy_copy,
    .rotate = dummy_rotate
};

void erase_augmented(struct node *node, struct node *parent,
                     const struct rb_augment_callbacks *augment) {
    augment->propagate(parent, 0);
    augment->copy(node, parent);
    augment->rotate(node, parent);
}

void erase_dummy(struct node *node, struct node *parent) {
    erase_augmented(node, parent, &dummy_callbacks);
}
```

```click
import click::separation;

verifying "rb_augment_callbacks.c";

contract void Propagate(struct node* node, struct node* stop) {
    requires node != 0;
    owns node->left;
    ensures node->left == old(node->left);
}

contract void Copy(struct node* old, struct node* new) {
    requires old != 0;
    requires new != 0;
    owns new->left;
    ensures new->left == old(new->left);
}

contract void Rotate(struct node* old, struct node* new) {
    requires new != 0;
    owns new->left;
    owns new->right;
    ensures new->left == old(new->left);
    ensures new->right == old(new->right);
}

resource callback_suite(augment: const struct rb_augment_callbacks*) {
    owns augment->propagate;
    owns augment->copy;
    owns augment->rotate;
    fact Propagate(augment->propagate);
    fact Copy(augment->copy);
    fact Rotate(augment->rotate);
}

void erase_augmented(struct node* node, struct node* parent,
                     const struct rb_augment_callbacks* augment) {
    views callback_suite(augment);
    requires node != 0;
    requires parent != 0;
    owns parent->left;
    owns parent->right;
    ensures parent->left == old(parent->left);
    ensures parent->right == old(parent->right);
} by {
    have separate(callback_suite(augment), memory(*parent)) by { close(); }
    observe(callback_suite(augment));
    apply(separation::contains_refl(memory(*parent)));
    apply(separation::separate_restrict(callback_suite(augment), memory(*parent), memory(augment->propagate), memory(*parent)));
    apply(separation::separate_restrict(callback_suite(augment), memory(*parent), memory(augment->copy), memory(*parent)));
    apply(separation::separate_restrict(callback_suite(augment), memory(*parent), memory(augment->rotate), memory(*parent)));
    apply(separation::separate_star(memory(augment->propagate), memory(augment->copy), memory(*parent)));
    apply(separation::contains_joined_ranges(augment as (int32 *), 0, 2, 4));
    apply(separation::separate_restrict(
        memory(augment->propagate) * memory(augment->copy), memory(*parent),
        memory((augment as (int32 *))[0..4]), memory(*parent)
    ));
    apply(separation::separate_star(memory((augment as (int32 *))[0..4]), memory(augment->rotate), memory(*parent)));
    apply(separation::contains_joined_ranges(augment as (int32 *), 0, 4, 6));
    apply(separation::separate_restrict(
        memory((augment as (int32 *))[0..4]) * memory(augment->rotate), memory(*parent),
        memory(*augment), memory(*parent)
    ));
    apply(separation::contains_subrange(parent as (int32 *), 0, 4, 0, 2));
    apply(separation::contains_subrange(parent as (int32 *), 0, 4, 2, 4));
    apply(separation::contains_refl(memory(*augment)));
    apply(separation::separate_restrict(memory(*augment), memory(*parent), memory(*augment), memory(parent->left)));
    apply(separation::separate_restrict(memory(*augment), memory(*parent), memory(*augment), memory(parent->right)));
    step();
    step();
    step();
}
```

```expect
pass
```
