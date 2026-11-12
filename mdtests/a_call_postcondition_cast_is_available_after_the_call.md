# A call's postcondition is available right after the call

`put` ensures that `old`'s parent word, masked and cast to a pointer, is
`new`. Right after `put(g, p)` that fact is exactly what `assumption` should
find. Here `p` is the result of a contracted call, and the caller holds `p`'s
word under another spelling, `n->rb_left`.

```c filename=call_cast.c
struct rb_node {
    unsigned long __rb_parent_color;
    struct rb_node *rb_right;
    struct rb_node *rb_left;
} __attribute__((aligned(sizeof(long))));
struct rb_node *get(struct rb_node *n) { return n->rb_left; }
void put(struct rb_node *old, struct rb_node *new) { old->__rb_parent_color = (unsigned long)new | 1; }
void use(struct rb_node *n, struct rb_node *g) { struct rb_node *p = get(n); put(g, p); }
```

```click
verifying "call_cast.c";
struct rb_node* get(struct rb_node* n) {
    views n->rb_left;
    ensures result == n->rb_left;
}
void put(struct rb_node* old, struct rb_node* new) {
    owns old->__rb_parent_color;
    owns new->__rb_parent_color;
    requires old != new;
    requires aligned(new, 8);
    ensures ((old->__rb_parent_color & ~3) as (struct rb_node *)) == new;
}
void use(struct rb_node* n, struct rb_node* g) {
    owns n->rb_left;
    owns g->__rb_parent_color;
    owns n->rb_left->__rb_parent_color;
    requires g != n->rb_left;
    requires aligned(n->rb_left, 8);
} by {
    step(); step(); step();
    have ((g->__rb_parent_color & ~3) as (struct rb_node *)) == p by { assumption(); }
    step_until(function.exit);
}
```

```expect
pass
```
