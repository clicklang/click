# A struct equality compares every field

`*dst == *src` at a struct type says the two structs hold the same value:
every field of one equals the same field of the other. `copy_both` copies
`x` and `y`, so it meets the claim.

```c filename=a_struct_equality_compares_every_field.c
struct pair { int32 x; int32 y; };

void copy_both(struct pair* dst, const struct pair* src) {
    dst->x = src->x;
    dst->y = src->y;
}
```

```click
verifying "a_struct_equality_compares_every_field.c";

void copy_both(struct pair* dst, const struct pair* src) {
    owns *dst;
    views *src;
    requires separate(memory(*dst), memory(*src));
    ensures *dst == *src;
}
```

```expect
pass
```
