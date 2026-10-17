# A named contract keeps the view of an authored pointer cast

Preparing the named contract must use the same enclosing-object view as the
resource instance created from its written `(void*)` cast. The original
pointer's member view establishes its own bounds; the widened cast alone
cannot establish bounds for that original pointer. The C read also verifies
through the instance, without granting access to another object.

```c filename=entry.c
struct rb_node { int32 flags; struct rb_node* left; struct rb_node* right; };
struct sized_node { struct rb_node rb; int32 size; };
int32 read_size(struct sized_node* node) { return node->size; }
```

```click
verifying "entry.c";
resource size_metadata(node: struct rb_node*) {
    field value: int32;
    owns ((struct sized_node*)(void*)node)->size;
    fact ((struct sized_node*)(void*)node)->size == value;
}
int32 read_size(struct sized_node* node) {
    requires node != 0;
    views node->size;
    owns parent: size_metadata((struct rb_node*)(void*)node);
    ensures result == old(parent.value);
} by { unfold(parent); execute(); fold(parent); simp(); }

contract int32 ReadSize(struct sized_node* node) {
    requires node != 0;
    views node->size;
    owns parent: size_metadata((struct rb_node*)(void*)node);
    ensures result == old(parent.value);
}
```

```expect
pass
```
