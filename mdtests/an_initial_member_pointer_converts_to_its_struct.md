# A pointer to an initial member converts to a pointer to its struct

A pointer to a structure's initial member, suitably converted, points to the
structure (C11 6.7.2.1p15). Here `member` is `&outer->inner`, whose bounds are
`inner`'s, and it is the initial member of `*outer`, so the conversion reaches
`outer->count`. Without the rule the read would be outside the subobject
`member` designates, as `a_void_cast_keeps_a_member_pointers_bounds.md` is.

```c filename=probe.c
struct inner { int32 tag; };
struct outer { struct inner inner; int32 count; };
int32 probe(struct outer* outer) {
    struct inner* member = &outer->inner;
    return ((struct outer*)(void*)member)->count;
}
```

```click
verifying "probe.c";
int32 probe(struct outer* outer) {
    views *outer;
    ensures result == outer->count;
}
```

```expect
pass
```
