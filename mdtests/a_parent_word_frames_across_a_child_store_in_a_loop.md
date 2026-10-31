# A parent word frames across a child-pointer store in a loop

The loop store changes the child's right link while preserving the pointer
field that names the child. Its explicit certificate uses the recorded write
footprint and separation; pointer reads retain both address and provenance even
when their internal names differ. The parent-word equality then follows by the
written alias rewrite and an available fact, without another transport search.

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
            have separate(memory(gparent->rb_left), memory(parent->rb_right));
            have gparent->rb_left == parent by { solve() using { parent == gparent->rb_left; }; }
            have separate(memory(gparent->rb_left), memory(gparent->rb_left->rb_right)) by {
                rewrite(gparent->rb_left == parent);
                assumption();
            }
            mark before_store;
            step();
            mark after_store;
            have gparent->rb_left == at(before_store, gparent->rb_left) by {
                transport_certificate {
                    premise 0: changes_only(before_store, after_store, memory(gparent->rb_left->rb_right))
                        => changes_only(before_store, after_store, memory(gparent->rb_left->rb_right));
                    premise 1: at(before_store, separate(memory(gparent->rb_left), memory(gparent->rb_left->rb_right)))
                        => at(before_store, separate(memory(gparent->rb_left), memory(gparent->rb_left->rb_right)));
                    preserve 0, 1 => gparent->rb_left == at(before_store, gparent->rb_left);
                    conclusion 2;
                }
            }
            have parent == at(before_store, gparent->rb_left) by { assumption(); }
            have parent->__rb_parent_color == at(before_store, parent->__rb_parent_color) by {
                rewrite(parent == at(before_store, gparent->rb_left));
                assumption();
            }
            have defined(gparent->rb_left) by {
                transport(defined(at(before_store, gparent->rb_left)), defined(gparent->rb_left)) using {
                    separate(memory(gparent->rb_left), memory(parent->rb_right));
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
pass
```
