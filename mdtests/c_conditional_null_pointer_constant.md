# A conditional with a null pointer constant has the pointer's type

When one arm of `?:` is a pointer and the other is a null pointer constant,
`0` or `(0 as (void *))`, the result has the pointer's type, as in C. The Linux
rbtree erase code writes `rebalance = (pc & 1) ? parent : ((void *)0);`.

```c filename=c_conditional_null_pointer_constant.c
struct node {
    int value;
};

struct node *keep(struct node *node, int32 pick) {
    struct node *result;
    result = pick ? node : ((void *)0);
    return result;
}

struct node *drop(struct node *node, int32 pick) {
    return pick ? ((void *)0) : node;
}
```

```click
verifying "c_conditional_null_pointer_constant.c";

struct node* keep(struct node* node, int32 pick) {
    requires pick == 0;
    ensures result == 0;
}

struct node* drop(struct node* node, int32 pick) {
    requires pick == 0;
    ensures result == node;
}
```

```expect
pass
```
