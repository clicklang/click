# A missing element behind a pointer chain prints as its place

`fill` stores `o->b->data[i]`, an element behind the pointer field `data` of
the struct `o->b` points at. The contract owns only `o->b->data[0..n]`. The
refusal names the element as `o->b->data[i]`, not as a byte offset from `o`
(design/place-based-resource-clauses.md, step 2).

```c filename=a_missing_element_behind_a_pointer_chain_prints_as_its_place.c
struct buf {
    int32* data;
};

struct outer {
    struct buf* b;
};

void fill(struct outer* o, int32 i, int32 n) {
    o->b->data[i] = 1;
}
```

```click
verifying "a_missing_element_behind_a_pointer_chain_prints_as_its_place.c";

void fill(struct outer* o, int32 i, int32 n) {
    owns *o;
    owns *o->b;
    owns o->b->data[0..n];
    requires 0 <= i and i <= n;
}
```

```expect
fail: missing resource fact `owns o->b->data[i]`
```
