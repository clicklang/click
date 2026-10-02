# An assignment cannot drop `const` implicitly

Only an explicit cast may drop `const`; an implicit conversion may not.

```c filename=c_const_implicit_assignment_rejected.c
struct node {
    int value;
};

int32 run(const struct node *view) {
    struct node *node;
    node = view;
    return 0;
}
```

```click
verifying "c_const_implicit_assignment_rejected.c";
```

```expect
fail:c_const_implicit_assignment_rejected.c:7: cannot discard const qualification from a pointer initializer
```
