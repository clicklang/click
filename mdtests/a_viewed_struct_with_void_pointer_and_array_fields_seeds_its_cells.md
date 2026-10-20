# A viewed struct with `void *` and array fields seeds its cells

Viewing a struct seeds one symbolic cell per scalar field and per element of
an array field. Only `int32`, `int64`, `int128`, and `uint8` array fields were
expanded; any other array field, including the `void *a[2]` child links of
musl's AVL `struct node` (`src/search/tsearch.h`), was seeded as one aggregate
cell and panicked. A `void *` field panicked as well, because its pointee has no
width. Array fields of every element type now seed per element, and a `void *`
cell stays unseeded, as static-storage seeding leaves it. `height` is musl's
`src/search/tsearch.c` helper, unchanged.

```c filename=tsearch_height.c
struct node {
	const void *key;
	void *a[2];
	int h;
};

static inline int height(struct node *n) { return n ? n->h : 0; }
```

```click
verifying "tsearch_height.c";

int32 height(struct node *n) {
    requires n != 0;
    views n[0..1];
    ensures result == n->h by auto();
}
```

```expect
pass
```
