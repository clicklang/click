# A pointer cell read at two pointer types is one value

A load's identity is its version point and its cell, never the type it is
decoded at (`design/loads.md`, "Pointers"): every object-pointer type decodes
one eight-byte cell to the same pointer. The `void *` field `h->data`, read
as declared and through an `int32 **` view of the same cell, is one pointer
value, so the two reads are equal with no fact to find.

```c filename=pointer_cell_two_types.c
struct holder {
    void *data;
    int32 n;
};

int32 *data_as_words(struct holder *h) {
    int32 **view = (void *)&h->data;
    return *view;
}
```

```click
verifying "pointer_cell_two_types.c";

int32 *data_as_words(struct holder *h) {
    views h->data;
    ensures result == h->data;
    ensures load<int32 *>(&h->data) == h->data;
}
```

```expect
pass
```
