# A struct pointer and a non-null `void *` arm are rejected

Only a null pointer constant takes the other arm's type. The conversion C
defines for an object pointer against a `void *` arm is not modeled.

```c filename=c_conditional_nonnull_void_pointer_rejected.c
struct node {
    int value;
};

struct node *pick(struct node *node, int *other, int32 which) {
    return which ? node : (void *)other;
}
```

```click
verifying "c_conditional_nonnull_void_pointer_rejected.c";
```

```expect
fail:c_conditional_nonnull_void_pointer_rejected.c:6: conditional operator branches have incompatible types
```
