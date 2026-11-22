# A struct equality is not its first field's

`copy_x` copies only `x`, so `*dst == *src` does not hold: `dst->y` keeps
whatever it held. The struct's value is all its fields, not the word at its
address.

```c filename=a_struct_equality_is_not_its_first_field.c
struct pair { int32 x; int32 y; };

void copy_x(struct pair* dst, const struct pair* src) {
    dst->x = src->x;
}
```

```click
verifying "a_struct_equality_is_not_its_first_field.c";

void copy_x(struct pair* dst, const struct pair* src) {
    owns *dst;
    views *src;
    requires separate(memory(*dst), memory(*src));
    ensures *dst == *src;
}
```

```expect
fail: did not retain a complete proof for `copy_x.ensures_0`
```
