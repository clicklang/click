# A chain of simple assignments stores one value in each target

In `a->f = b = value`, the inner assignment happens once and its value is what the outer store writes. The inner assignment is unsequenced relative to evaluating the outer lvalue, which C leaves undefined only if that evaluation reads the assigned variable. Here it reads other named locals only. The outer store is sequenced after the value is read, so it does not matter whether the two pointers alias. The Linux rbtree erase code writes `tmp->__rb_parent_color = pc = node->__rb_parent_color;`.

```c filename=c_chained_assignment.c
struct node {
    unsigned long color;
    struct node *next;
};

unsigned long copy(struct node *to, struct node *from) {
    unsigned long pc;
    to->color = pc = from->color;
    return pc;
}

unsigned long same(struct node *node) {
    unsigned long pc;
    node->color = pc = node->color;
    return pc;
}

int32 three(struct node *to, struct node *from) {
    unsigned long a;
    unsigned long b;
    to->color = a = b = from->color;
    return a == b;
}
```

```click
verifying "c_chained_assignment.c";

uint64 copy(struct node* to, struct node* from) {
    owns to->color;
    views from->color;
    ensures result == old(from->color) by auto;
    ensures to->color == old(from->color) by auto;
}

uint64 same(struct node* node) {
    owns node->color;
    ensures result == old(node->color) by auto;
    ensures node->color == old(node->color) by auto;
}

int32 three(struct node* to, struct node* from) {
    owns to->color;
    views from->color;
    ensures result == 1 by auto;
}
```

```expect
pass
```
