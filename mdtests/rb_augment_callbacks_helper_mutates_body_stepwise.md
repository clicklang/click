# A viewed suite opened around single steps closes like one opened around `step_until(function.exit)`

The same helper as `rb_augment_callbacks_helper_mutates_body.md`, with all
three callback calls taken with `step()` inside the open. The body stops
short of the function exit, so the close is checked at once. It must record
the viewed suite as the state holds it: a viewed head closes through the same
evidence an owned one does.

```c filename=rb_augment_callbacks_mutates_body_stepwise.c
struct node {
    struct node *left;
    struct node *right;
};

struct rb_augment_callbacks {
    void (*propagate)(struct node *node, struct node *stop);
    void (*copy)(struct node *old, struct node *new);
    void (*rotate)(struct node *old, struct node *new);
};

void dummy_propagate(struct node *node, struct node *stop) {
    node->left = stop;
}
void dummy_copy(struct node *old, struct node *new) { }
void dummy_rotate(struct node *old, struct node *new) { }

void erase_mutating(struct node *node, struct node *parent,
                    struct rb_augment_callbacks *augment) {
    augment->propagate(parent, 0);
    augment->copy(node, parent);
    augment->rotate(node, parent);
}
```

```click
abstract resource spare(value: int32);

import click::separation;

verifying "rb_augment_callbacks_mutates_body_stepwise.c";

contract void Propagate(struct node* node, struct node* stop) {
    requires node != 0;
    owns node->left;
    ensures node->left == stop;
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

resource callback_suite(augment: struct rb_augment_callbacks*) {
    owns augment->propagate;
    owns augment->copy;
    owns augment->rotate;
    fact Propagate(augment->propagate);
    fact Copy(augment->copy);
    fact Rotate(augment->rotate);
}

void erase_mutating(struct node* node, struct node* parent,
                    struct rb_augment_callbacks* augment) {
    requires node != 0;
    requires parent != 0;
    requires separate(memory(*augment), memory(*parent));
    owns parent->left;
    owns parent->right;
    views callback_suite(augment);
    owns spare(7);
    ensures parent->left == 0;
    ensures parent->right == old(parent->right);
} by {
    with(callback_suite(augment)) {
        apply(separation::contains_refl(memory(*augment))) using {};
        apply(separation::contains_subrange(augment as (int32*), 0, 6, 0, 2)) using { 0 <= 0; 0 <= 2; 2 <= 6; };
        apply(separation::contains_subrange(augment as (int32*), 0, 6, 2, 4)) using { 0 <= 2; 2 <= 4; 4 <= 6; };
        apply(separation::contains_subrange(augment as (int32*), 0, 6, 4, 6)) using { 0 <= 4; 4 <= 6; 6 <= 6; };
        apply(separation::contains_subrange(parent as (int32*), 0, 4, 0, 2)) using { 0 <= 0; 0 <= 2; 2 <= 4; };
        have separate(memory(parent->left), memory(*augment)) by {
            apply(separation::separate_restrict(memory(*parent), memory(*augment), memory(parent->left), memory(*augment)));
        }
        apply(separation::contains_subrange(parent as (int32*), 0, 4, 2, 4)) using { 0 <= 2; 2 <= 4; 4 <= 4; };
        have separate(memory(parent->right), memory(*augment)) by {
            apply(separation::separate_restrict(memory(*parent), memory(*augment), memory(parent->right), memory(*augment)));
        }
        apply(separation::separate_star(memory(parent->left), memory(parent->right), memory(*augment))) using {
            separate(memory(parent->left), memory(*augment));
            separate(memory(parent->right), memory(*augment));
        };
        mark before_propagate;
        step();
        have contains(memory(parent->left), statement(0).footprint) by { known(); }
        apply(separation::separate_restrict(memory(parent->left), memory(*augment), statement(0).footprint, memory(augment->propagate)));
        have augment->propagate == at(before_propagate, augment->propagate) by { preserve(memory(augment->propagate), statement(0)); }
        apply(separation::separate_restrict(memory(parent->left), memory(*augment), statement(0).footprint, memory(augment->copy)));
        have augment->copy == at(before_propagate, augment->copy) by { preserve(memory(augment->copy), statement(0)); }
        apply(separation::separate_restrict(memory(parent->left), memory(*augment), statement(0).footprint, memory(augment->rotate)));
        have augment->rotate == at(before_propagate, augment->rotate) by { preserve(memory(augment->rotate), statement(0)); }
        mark before_copy;
        step();
        have contains(memory(parent->left), statement(1).footprint) by { known(); }
        apply(separation::separate_restrict(memory(parent->left), memory(*augment), statement(1).footprint, memory(augment->propagate)));
        have augment->propagate == at(before_copy, augment->propagate) by { preserve(memory(augment->propagate), statement(1)); }
        apply(separation::separate_restrict(memory(parent->left), memory(*augment), statement(1).footprint, memory(augment->copy)));
        have augment->copy == at(before_copy, augment->copy) by { preserve(memory(augment->copy), statement(1)); }
        apply(separation::separate_restrict(memory(parent->left), memory(*augment), statement(1).footprint, memory(augment->rotate)));
        have augment->rotate == at(before_copy, augment->rotate) by { preserve(memory(augment->rotate), statement(1)); }
        mark before_rotate;
        step();
        have contains(memory(parent->left) * memory(parent->right), statement(2).footprint) by { known(); }
        apply(separation::separate_restrict(memory(parent->left) * memory(parent->right), memory(*augment), statement(2).footprint, memory(augment->propagate)));
        have augment->propagate == at(before_rotate, augment->propagate) by { preserve(memory(augment->propagate), statement(2)); }
        apply(separation::separate_restrict(memory(parent->left) * memory(parent->right), memory(*augment), statement(2).footprint, memory(augment->copy)));
        have augment->copy == at(before_rotate, augment->copy) by { preserve(memory(augment->copy), statement(2)); }
        apply(separation::separate_restrict(memory(parent->left) * memory(parent->right), memory(*augment), statement(2).footprint, memory(augment->rotate)));
        have augment->rotate == at(before_rotate, augment->rotate) by { preserve(memory(augment->rotate), statement(2)); }
    }
}
```

```expect
pass
```
