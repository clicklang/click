# Conditional arms must point to the same struct type

Pointers to different struct types are not compatible C types, even though
they share a representation.

```c filename=c_conditional_struct_pointer_mismatch_rejected.c
struct left {
    int value;
};

struct right {
    int value;
};

struct left *pick(struct left *a, struct right *b, int32 which) {
    return which ? a : b;
}
```

```click
verifying "c_conditional_struct_pointer_mismatch_rejected.c";
```

```expect
fail:c_conditional_struct_pointer_mismatch_rejected.c:10: conditional operator branches have incompatible types `struct left *` and `struct right *`
```
