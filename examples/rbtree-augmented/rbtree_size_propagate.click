// First visited leaf: both the early break and the parent advance restore size.
verifying "rbtree_size_propagate.c";
verifying "rbtree_size_compute.c";
verifying "rbtree_size_copy.c";
import "rbtree_size_compute.click";

function propagate_remaining(rb: struct rb_node*, stop: struct rb_node*) -> int32 {
    if rb == stop { 0 } else { 1 }
}

resource leaf_links(rb: struct rb_node*, stop: struct rb_node*) {
    field word: uint64;
    fact rb->__rb_parent_color == word;
    owns rb->__rb_parent_color;
    owns rb->rb_left;
    owns rb->rb_right;
    fact rb != 0;
    fact rb->rb_left == 0;
    fact rb->rb_right == 0;
    fact aligned(stop, 8);
    fact rb->__rb_parent_color == address(stop) + (rb->__rb_parent_color & 1);
}

void sized_propagate(struct rb_node* rb, struct rb_node* stop) {
    owns metadata: size_metadata(rb);
    owns links: leaf_links(rb, stop);
    requires rb != stop;
    ensures metadata.value == 1;
    ensures links.word == old(links.word);
} by {
    apply(compute_size_has_size_contract());
    loop {
        decreases propagate_remaining(rb, stop);
        owns metadata: size_metadata(old(rb));
        owns links: leaf_links(old(rb), stop);
        invariant old(rb) != stop;
        invariant links.word == old(links.word);
        invariant rb == old(rb) or rb == stop;
        invariant metadata.value == 1 or rb == old(rb);
        initialize by simp();
        preserve by {
            have rb == old(rb) by {
                cases {
                    rb == old(rb) => { assumption(); }
                    rb == stop => { contradiction(rb == stop); }
                }
            }
            have propagate_remaining(rb, stop) == 1 by {
                unfold(propagate_remaining(rb, stop));
                normalize() using { rb != stop; };
            }
            unfold(links);
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            let left = fold(optional_size(node->rb.rb_left), { value: 0 });
            let right = fold(optional_size(node->rb.rb_right), { value: 0 });
            let { result: status } = step(ComputeSize, { parent: metadata, left: left, right: right });
            have metadata.value == 1 by {
                rewrite(metadata.value == 1 + left.value + right.value);
                rewrite(left.value == 0);
                rewrite(right.value == 0);
                normalize();
            }
            unfold(left);
            unfold(right);
            fold(links);
            if status != 0 {
                step();
                step();
            } else {
                step();
                step();
                step();
                have rb == stop by { assumption(); }
                have propagate_remaining(rb, stop) == 0 by {
                    unfold(propagate_remaining(rb, stop));
                    normalize() using { rb == stop; };
                }
                have metadata.value == 1 by { assumption(); }
                have metadata.value == 1 or rb == old(rb) by { assumption(); }
            }
        }
    }
    execute();
    simp();
}
