# A missing element of an array field prints as its place

`fill` stores `p->a[i]`, but the contract owns only `p->a[2..6]`. The array
is a field of the struct `p` points at, and the field does not start the
struct. The refusal names the element as `p->a[i]` and compares its bounds as
indices of `p->a`, not as byte offsets from `p`
(design/place-based-resource-clauses.md, step 2).

```c filename=a_missing_array_field_element_prints_as_its_place.c
struct counts {
    int32 n;
    int32 a[8];
};

void fill(struct counts* p, int32 i) {
    p->a[i] = 1;
}
```

```click
verifying "a_missing_array_field_element_prints_as_its_place.c";

void fill(struct counts* p, int32 i) {
    owns p->a[2..6];
    requires 0 <= i and i < 8;
}
```

```expect
fail: held `owns p->a[2..6]` covers `p->a[i]` only when `2 <= i` and `(i + 1) <= 6`
```
