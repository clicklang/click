# A named contract keeps the view of an authored pointer cast

Preparing the named contract must use the same enclosing-object view as the
resource instance created from its written `(void*)` cast. The original
pointer's `viewable` precondition describes the original member. The C read
follows the same cast as the owned resource, so the proof uses the instance's
authority for that access.

```c filename=entry.c
struct rb_node { int32 flags; struct rb_node* left; struct rb_node* right; };
struct sized_node { struct rb_node rb; int32 size; };
int32 read_size(struct sized_node* node) {
    return ((struct sized_node *)(void *)(struct rb_node *)(void *)node)->size;
}
```

```click
verifying "entry.c";
resource size_metadata(node: struct rb_node*) {
    field value: int32;
    owns (node as (void *) as (struct sized_node *))->size;
    fact (node as (void *) as (struct sized_node *))->size == value;
}
int32 read_size(struct sized_node* node) {
    requires node != 0;
    requires viewable(node->size);
    owns parent: size_metadata(node as (void *) as (struct rb_node *));
    ensures result == old(parent.value);
} by { unfold(parent); step_until(function.exit); fold(parent); solve(); }

contract int32 ReadSize(struct sized_node* node) {
    requires node != 0;
    requires viewable(node->size);
    owns parent: size_metadata(node as (void *) as (struct rb_node *));
    ensures result == old(parent.value);
}
```

```expect
pass
```
