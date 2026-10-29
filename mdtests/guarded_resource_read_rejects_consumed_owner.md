# Guarded resource facts survive a disjoint store

```c filename=guarded.c
struct base { struct base* left; struct base* right; uint64 padding; };
struct cell { struct base base; int32 value; };
void consume_child(struct base *p);
int32 f(struct cell* root) {
    struct base* child = root->base.left;
    int32 value = ((struct cell*)(void*)child)->value;
    root->value = value;
    consume_child(child);
    return ((struct cell*)(void*)child)->value;
}
```

```click
verifying "guarded.c";
resource child_value(p: struct base*) {
    field number: int32;
    if p != 0 {
        owns (p as (void *) as (struct cell *))->value;
        fact (p as (void *) as (struct cell *))->value == number;
    }
}
extern void consume_child(struct base *p) {
    consumes state: child_value(p);
}
int32 f(struct cell* root) {
    requires root != 0;
    views root->base.left;
    consumes child: child_value(root->base.left);
    owns root->value;
    requires root->base.left != 0;
    requires root->base.left != root as (void *) as (struct base *);
    ensures result == old(child.number);
    ensures root->value == old(child.number);
} by {
    unfold(child);
    have separate(memory((root->base.left as (void *) as (struct cell *))->value), memory(root->value));
    mark before_store;
    step(); step(); step(); step(); step();
    have (root->base.left as (void *) as (struct cell *))->value == at(before_store, (root->base.left as (void *) as (struct cell *))->value) by {
        transport(at(before_store, (root->base.left as (void *) as (struct cell *))->value) == at(before_store, (root->base.left as (void *) as (struct cell *))->value),
                  (root->base.left as (void *) as (struct cell *))->value == at(before_store, (root->base.left as (void *) as (struct cell *))->value)) using {
            separate(memory((root->base.left as (void *) as (struct cell *))->value), memory(root->value));
        };
    }
    fold(child); step(); step(); solve();
}
```

```expect
fail: missing resource fact
```
