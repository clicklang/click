// First visited leaf: both the early break and the parent advance restore size.
verifying "rbtree_size_propagate.c";
verifying "rbtree_size_compute.c";
verifying "rbtree_size_copy.c";
import "rbtree_size_compute.click";

// The variant observes addresses, so its arguments need no pointee domain.
function propagate_remaining(rb: void*, stop: void*) -> int32 {
    if address(rb) == address(stop) { 0 } else { 1 }
}

resource leaf_parent_word(rb: struct rb_node*, stop: struct rb_node*) {
    field word: uint64;
    owns rb->__rb_parent_color;
    fact rb->__rb_parent_color == word;
    fact aligned(stop, 8);
    fact rb->__rb_parent_color == address(stop) + (rb->__rb_parent_color & 1);
    fact ((rb->__rb_parent_color & ~3) as (struct rb_node *)) == stop;
}

resource leaf_links(rb: struct rb_node*, stop: struct rb_node*) {
    field word: uint64;
    owns parent: leaf_parent_word(rb, stop);
    owns rb->rb_left;
    owns rb->rb_right;
    fact parent.word == word;
    fact rb != 0;
    fact rb->rb_left == 0;
    fact rb->rb_right == 0;
}

void sized_propagate(struct rb_node* rb, struct rb_node* stop) {
    owns metadata: size_metadata(rb);
    owns links: leaf_links(rb, stop);
    requires address(rb) != address(stop);
    ensures metadata.value == 1;
    ensures links.word == old(links.word);
} by {
    loop {
        decreases propagate_remaining(rb, stop);
        owns metadata: size_metadata(old(rb));
        owns links: leaf_links(old(rb), stop);
        invariant old(address(rb)) != address(stop);
        invariant links.word == old(links.word);
        invariant rb == old(rb) or rb == stop;
        invariant metadata.value == 1 or rb == old(rb);
        initialize by close();
        maintain by {
            have rb == old(rb) by {
                cases {
                    rb == old(rb) => { close(); }
                    rb == stop => {
                        have address(rb) == address(stop) by { rewrite(rb, stop); close(); }
                        contradiction(address(rb) == address(stop));
                    }
                }
            }
            have address(rb) != address(stop) by { rewrite(rb, old(rb)); close(); }
            have propagate_remaining(rb, stop) == 1 by {
                unfold(propagate_remaining(rb, stop));
                close() using { address(rb) != address(stop); };
            }
            // Expose the child links and keep the packed parent word folded across compute_size.
            mark leaf;
            let { parent: parent_word } = unfold(links);
            step_until(loop(0).statement(1).entry);
            have address(&node->rb) == address(old(rb)) by {
                normalize() using { rb == old(rb); };
            }
            have node->rb.rb_left == 0 by {
                normalize() using {
                    address(&node->rb) == address(old(rb));
                    old(rb)->rb_left == 0;
                };
            }
            have node->rb.rb_right == 0 by {
                normalize() using {
                    address(&node->rb) == address(old(rb));
                    old(rb)->rb_right == 0;
                };
            }
            let left = fold(optional_size(0), { value: 0 });
            let right = fold(optional_size(0), { value: 0 });
            let { result: status } = step(compute_size, { parent: metadata, left: left, right: right });
            have metadata.value == 1 by {
                rewrite(metadata.value, 1 + left.value + right.value);
                rewrite(left.value, 0);
                rewrite(right.value, 0);
                close();
            }
            unfold(left);
            unfold(right);
            have old(rb)->rb_left == 0 by close();
            have old(rb)->rb_right == 0 by close();
            if status != 0 {
                let links = fold(leaf_links(old(rb), stop), {
                    word: at(leaf, links.word), parent: parent_word
                });
                step();
                step();
            } else {
                observe(parent_word);
                step_until(loop.back_edge);
                have rb == stop by { close(); }
                let links = fold(leaf_links(old(rb), stop), {
                    word: at(leaf, links.word), parent: parent_word
                });
                have propagate_remaining(rb, stop) == 0 by {
                    unfold(propagate_remaining(rb, stop));
                }
                have metadata.value == 1 by { close(); }
                have metadata.value == 1 or rb == old(rb) by { close(); }
            }
        }
    }
}
