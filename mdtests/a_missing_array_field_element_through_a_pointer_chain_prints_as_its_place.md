# A missing array field element through a pointer chain prints as its place

`fill` stores `h->in->a[i]`: an element of an array field of the struct that
the pointer field `h->in` points at. The contract owns only `h->in->a[0..2]`.
The refusal names the element through the chain as `h->in->a[i]`, not as a
byte offset from `h` (design/place-based-resource-clauses.md, step 2).

```c filename=a_missing_array_field_element_through_a_pointer_chain_prints_as_its_place.c
struct inner {
    int32 n;
    int32 a[4];
};

struct holder {
    struct inner* in;
};

void fill(struct holder* h, int32 i) {
    h->in->a[i] = 1;
}
```

```click
verifying "a_missing_array_field_element_through_a_pointer_chain_prints_as_its_place.c";

void fill(struct holder* h, int32 i) {
    owns *h;
    owns h->in->n;
    owns h->in->a[0..2];
    requires 0 <= i and i < 4;
}
```

```expect
fail: missing resource fact `owns h->in->a[i]`
```
