# A pointer view stays defined beside a seeded field

The owned size field creates a sparse scalar run. Its indexed span also
covers the child pointers, where the run only has holes. Those holes do not
make the exact pointer slots ambiguous.

```c filename=pointer_view_beside_seeded_field.c
struct node {
    unsigned long tag;
    struct node *right;
    struct node *left;
};

struct sized_node {
    struct node links;
    int32 size;
};

int32 inspect_links(struct node *node) {
    return 0;
}
```

```click
verifying "pointer_view_beside_seeded_field.c";

resource cache(node: struct node*) {
    field value: int32;
    owns (node as (uint8 *) as (struct sized_node *))->size;
    fact (node as (uint8 *) as (struct sized_node *))->size == value;
}

int32 inspect_links(struct node* node) {
    requires node != 0;
    views (node as (uint8 *) as (struct sized_node *))->links.right;
    views (node as (uint8 *) as (struct sized_node *))->links.left;
    owns metadata: cache(node);
    ensures result == 0;
} by {
    have defined((node as (uint8 *) as (struct sized_node *))->links.right) by close();
    have defined((node as (uint8 *) as (struct sized_node *))->links.left) by close();
    step();
    close();
}
```

```expect
pass
```
