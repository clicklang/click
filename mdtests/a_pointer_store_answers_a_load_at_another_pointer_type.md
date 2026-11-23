# A pointer store answers a load at another pointer type

A store of a pointer writes the cell's bytes, and a later load of exactly that
cell at any object-pointer type reads the stored pointer (`design/loads.md`,
"Pointers"). Here `h->data` is a `void *` field: the function stores an
`int32 *` through an `int32 **` view of the cell, and the postconditions read
the field at its declared `void *` type and at `int32 *`. The store answers
both reads, so each is `p`.

```c filename=pointer_store_other_type.c
struct holder {
    void *data;
    int32 n;
};

void set_words(struct holder *h, int32 *p) {
    int32 **view = (void *)&h->data;
    *view = p;
}
```

```click
verifying "pointer_store_other_type.c";

void set_words(struct holder *h, int32 *p) {
    owns h->data;
    ensures h->data == p;
    ensures load<int32 *>(&h->data) == p;
}
```

```expect
pass
```
