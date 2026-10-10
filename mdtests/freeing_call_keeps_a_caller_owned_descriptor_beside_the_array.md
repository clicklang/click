# Freeing call keeps a caller-owned descriptor beside the array

`buf_destroy` frees a buffer's `int` array, consuming both its allocation
authority, a byte range whose length is the symbolic `capacity * 4`, and its
four-byte element range. The caller keeps `*r`, a separately owned
descriptor. The call rule must show the kept descriptor survives beside the
freed bytes, which compares a byte-width range with a symbolic end against an
owned range of another element width; a coverage check that mishandles that
width mismatch drops the descriptor or accepts the free unsoundly.

```c filename=freeing_call_keeps_a_caller_owned_descriptor_beside_the_array.c
struct buf { int *data; int capacity; };
struct region { int start; };
void buf_destroy(struct buf *b) { free(b->data); }
void teardown(struct buf *b, struct region *r) { buf_destroy(b); }
```

```click
verifying "freeing_call_keeps_a_caller_owned_descriptor_beside_the_array.c";

void buf_destroy(struct buf* b) {
    owns *b;
    consumes allocation(b->data, b->capacity * 4);
    consumes b->data[0..b->capacity];
    requires 1 <= b->capacity;
    requires b->capacity <= 536870911;
} by {
    execute();
    simp();
}

void teardown(struct buf* b, struct region* r) {
    owns *b;
    consumes allocation(b->data, b->capacity * 4);
    consumes b->data[0..b->capacity];
    requires 1 <= b->capacity;
    requires b->capacity <= 536870911;
    owns *r;
} by {
    execute();
    simp();
}
```

```expect
pass
```
