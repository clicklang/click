# A byte copy through a pointer field keeps its source readable

This is the raw-pointer control for the Bitcoin read32 cursor witness. The
source view and destination transfer are explicit; the copy must preserve the
pointer field and the second source byte across its first store.

```c filename=cursor.c
struct Cursor { const uint8* data; };
void copy(struct Cursor* c, uint8* d) {
    d[0] = c->data[0];
    d[1] = c->data[1];
}
```

```click
verifying "cursor.c";
void copy(struct Cursor* c, uint8* d) {
    requires separate(memory(d[0..2]), memory(c->data[0..2]));
    owns c->data;
    views c->data[0..2];
    consumes uninitialized(d[0..2]);
    produces d[0..2];
    ensures d[0] == old(c->data[0]);
    ensures d[1] == old(c->data[1]);
}
```

```expect
pass
```
