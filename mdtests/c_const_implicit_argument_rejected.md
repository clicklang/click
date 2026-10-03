# An argument cannot drop `const` implicitly

Only an explicit cast may drop `const`; an implicit conversion may not.

```c filename=c_const_implicit_argument_rejected.c
struct node {
    int value;
};

int take(struct node *node);

int32 run(const struct node *view) {
    return take(view);
}
```

```click
verifying "c_const_implicit_argument_rejected.c";
```

```expect
fail:c_const_implicit_argument_rejected.c:8: cannot discard const qualification from a pointer initializer
```
