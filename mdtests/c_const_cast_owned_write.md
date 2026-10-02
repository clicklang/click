# A cast may drop `const` from a view of mutable storage

C lets an explicit cast drop `const`. When the storage behind the pointer is
not itself const, the write is defined and is checked like any other store:
it needs write authority. The Linux rbtree traversal functions return their
`const struct rb_node *` argument through such a cast.

```c filename=c_const_cast_owned_write.c
struct node {
    int value;
};

int32 set(const struct node *view) {
    struct node *node = (struct node *)view;
    node->value = 7;
    return view->value;
}

struct node *same(const struct node *view) {
    return (struct node *)view;
}
```

```click
verifying "c_const_cast_owned_write.c";

int32 set(const struct node* view) {
    owns view->value;
    ensures result == 7 by auto;
    ensures view->value == 7 by auto;
}

struct node* same(const struct node* view) {
    ensures result == view by auto;
}
```

```expect
pass
```
