# A parent word frames across a child-pointer store in a loop

The Linux rbtree insertion rotation (`__rb_insert`) keeps a node's
eight-byte `__rb_parent_color` word while it rewrites the node's
`rb_right` link with `WRITE_ONCE`. Inside the loop the store's address is
the owned node the invariant names, `g->rb_left`, so the transport lists that
alias. The two reads of the `unsigned long` word are 64-bit loads; the
checked load history frames them across the store exactly as it frames a
32-bit read. Before that route covered 64-bit equalities, this transport
was refused with "found no frame evidence" unless lowering happened to give
both reads one canonical name, which depended on the function's name.

```c filename=parent_word.c
#define WRITE_ONCE(x, value) ({ typeof(x) __value = (value); (*(volatile typeof(x) *)&(x)) = __value; __value; })
struct rb_node {
    unsigned long __rb_parent_color;
    struct rb_node *rb_right;
    struct rb_node *rb_left;
};
void rotate_child_link(struct rb_node *gparent, struct rb_node *tmp) {
    struct rb_node *parent = gparent->rb_left;
    while (1) {
        WRITE_ONCE(parent->rb_right, tmp);
        break;
    }
}
```

```click
verifying "parent_word.c";
resource node_at(p: struct rb_node*) {
    field v: int32;
    fact p != 0;
    owns p->__rb_parent_color;
    owns p->rb_right;
    owns p->rb_left;
}
resource left_child(g: struct rb_node*) {
    field v: int32;
    owns g->rb_left;
    owns child: node_at(g->rb_left);
    fact child.v == v;
}
void rotate_child_link(struct rb_node* gparent, struct rb_node* tmp) {
    owns s: left_child(gparent);
} by {
    execute_until(loop(0));
    loop {
        owns s: left_child(gparent);
        invariant parent == gparent->rb_left;
        invariant parent == old(gparent->rb_left);
        decreases 0;
        initialize by simp();
        preserve by {
            let { child: c } = unfold(s);
            unfold(c);
            mark before_store;
            step();
            have parent->__rb_parent_color == at(before_store, parent->__rb_parent_color) by {
                transport(at(before_store, parent->__rb_parent_color) == at(before_store, parent->__rb_parent_color),
                          parent->__rb_parent_color == at(before_store, parent->__rb_parent_color)) using {
                    parent == gparent->rb_left;
                };
            }
            let c = fold(node_at(gparent->rb_left), { v: 0 });
            let s = fold(left_child(gparent), { v: 0 }, { child: c });
            step();
        }
    }
    execute();
}
```

```expect
pass
```
