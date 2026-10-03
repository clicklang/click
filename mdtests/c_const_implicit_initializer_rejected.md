# An initializer cannot drop `const` implicitly

Only an explicit cast may drop `const`; an implicit conversion may not.

```c filename=c_const_implicit_initializer_rejected.c
struct node {
    int value;
};

int32 run(const struct node *view) {
    struct node *node = view;
    return 0;
}
```

```click
verifying "c_const_implicit_initializer_rejected.c";
```

```expect
fail:c_const_implicit_initializer_rejected.c:6: cannot discard const qualification from a pointer initializer
```
