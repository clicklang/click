# A proof covers both values of `__builtin_constant_p`

Whether the compiler folds the operand to a constant depends on optimization, so the result is an unknown 0 or 1. The operand is not evaluated. A function is verified only if its claim holds on both outcomes, so no claim depends on which arm the compiler kept. The second function has the shape of the Linux `rcu_assign_pointer` macro.

```c filename=c_builtin_constant_p.c
struct node {
    struct node *left;
};

int32 either(int32 value) {
    if (__builtin_constant_p(value))
        return value;
    else
        return value + 0;
}

int32 flag(int32 value) {
    return __builtin_constant_p(value);
}

void assign(struct node *parent, struct node *new) {
    unsigned long v = (unsigned long)(new);
    if (__builtin_constant_p(new) && (v) == (unsigned long)((void *)0))
        parent->left = (struct node *)(v);
    else
        parent->left = (struct node *)v;
}
```

```click
verifying "c_builtin_constant_p.c";

int32 either(int32 value) {
    ensures result == value by auto;
}

int32 flag(int32 value) {
    ensures result == 0 or result == 1 by auto;
}

void assign(struct node* parent, struct node* new) {
    owns parent->left;
    ensures parent->left == new by auto;
}
```

```expect
pass
```
