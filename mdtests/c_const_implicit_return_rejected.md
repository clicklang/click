# A return cannot drop `const` implicitly

Only an explicit cast may drop `const`; an implicit conversion may not.

```c filename=c_const_implicit_return_rejected.c
struct node {
    int value;
};

struct node *run(const struct node *view) {
    return view;
}
```

```click
verifying "c_const_implicit_return_rejected.c";
```

```expect
fail:c_const_implicit_return_rejected.c:6: cannot discard const qualification from a pointer initializer
```
