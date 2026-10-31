# A store to the parent word itself is not framed

The companion of `a_parent_word_frames_across_a_child_store_in_a_loop.md`.
Here the loop body stores to the parent word itself, so its two 64-bit reads
are different versions of the cell and the same transport is refused.

```c filename=parent_word_store.c
#define WRITE_ONCE(x, value) ({ typeof(x) __value = (value); (*(volatile typeof(x) *)&(x)) = __value; __value; })
struct rb_node {
    unsigned long __rb_parent_color;
    struct rb_node *rb_right;
    struct rb_node *rb_left;
};
void rotate_child_link(struct rb_node *gparent, struct rb_node *tmp) {
    struct rb_node *parent = gparent->rb_left;
    while (1) {
        WRITE_ONCE(parent->__rb_parent_color, 1);
        break;
    }
}
```

```click
verifying "parent_word_store.c";
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
    step_until(loop(0));
    loop {
        owns s: left_child(gparent);
        invariant parent == gparent->rb_left;
        invariant parent == old(gparent->rb_left);
        decreases 0;
        initialize by solve();
        preserve by {
            let { child: c } = unfold(s);
            unfold(c);
            have separate(memory(gparent->rb_left), memory(parent->__rb_parent_color));
            have gparent->rb_left == parent by { solve() using { parent == gparent->rb_left; }; }
            have separate(memory(gparent->rb_left), memory(gparent->rb_left->__rb_parent_color)) by {
                rewrite(gparent->rb_left == parent);
                assumption();
            }
            mark before_store;
            step();
            mark after_store;
            have gparent->rb_left == at(before_store, gparent->rb_left) by {
                transport_certificate {
                    premise 0: changes_only(before_store, after_store, memory(gparent->rb_left->__rb_parent_color))
                        => changes_only(before_store, after_store, memory(gparent->rb_left->__rb_parent_color));
                    premise 1: at(before_store, separate(memory(gparent->rb_left), memory(gparent->rb_left->__rb_parent_color)))
                        => at(before_store, separate(memory(gparent->rb_left), memory(gparent->rb_left->__rb_parent_color)));
                    preserve 0, 1 => gparent->rb_left == at(before_store, gparent->rb_left);
                    conclusion 2;
                }
            }
            have parent == at(before_store, gparent->rb_left) by { assumption(); }
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
}
```

```expect
fail: `transport using` found no frame evidence carrying its source fact to the target's state
```
