# An owned suite's callbacks stay callable after the open closes

The callback suite is opened once; the first callback stores through its owned
node link and the second is still authorized inside the open. The open then
closes before the third call, and the cells the body exposed, `augment->rotate`
among them, go back into the folded suite. The third call is still authorized:
holding the suite lets C read the memory it owns directly, so the call reads
the callback pointer through the folded suite, and the suite's `Rotate` fact
describes that cell for as long as the suite stays folded. A write to the
cell would need `unfold`, which retires the read.

```c filename=rb_augment_callbacks_call_after_close.c
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

verifying "rb_augment_callbacks_call_after_close.c";

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
    owns callback_suite(augment);
    consumes spare(7);
    produces spare(7);
    ensures parent->left == 0;
    ensures parent->right == old(parent->right);
} by {
    open(callback_suite(augment)) {
        step();
        step();
    }
    execute();
    simp();
}
```

```expect
pass
```
