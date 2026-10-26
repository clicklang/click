verifying "rbtree_size_copy.c";
verifying "rbtree_size_compute.c";
verifying "rbtree_size_rotate.c";
import "rbtree_size_metadata.click";
import "rbtree_size_rotate.click";

// Copying the cache cells must preserve the independently owned tree links.
contract void CopySizedStructure(struct rb_node* rb_old, struct rb_node* rb_new) {
    owns source_tree: rb_at(rb_old);
    owns target_tree: rb_at(rb_new);
    owns source: size_metadata(rb_old);
    owns target: size_metadata(rb_new);
    ensures source_tree.model == old(source_tree.model);
    ensures target_tree.model == old(target_tree.model);
    ensures source.value == old(source.value);
    ensures target.value == old(source.value);
}

theorem sized_copy_preserves_structure()
executes sized_copy(struct rb_node* rb_old, struct rb_node* rb_new) {
    ensures CopySizedStructure(&sized_copy) as {
        source_tree: source_tree, target_tree: target_tree, source: source, target: target
    } by {
        step(sized_copy, { source: source, target: target });
        solve();
    }
}

// Rotation changes cache cells and preserves independently owned tree links.
contract void RotateSizedStructure(struct rb_node* rb_old, struct rb_node* rb_new) {
    requires rb_old != 0;
    requires rb_new != 0;
    requires rb_old != rb_new;
    owns structure: rb_at(rb_new);
    views (rb_old as (void *) as (struct sized_node *))->rb.rb_left;
    views (rb_old as (void *) as (struct sized_node *))->rb.rb_right;
    owns source: size_metadata(rb_old);
    owns target: size_metadata(rb_new);
    owns left: optional_size((rb_old as (void *) as (struct sized_node *))->rb.rb_left);
    owns right: optional_size((rb_old as (void *) as (struct sized_node *))->rb.rb_right);
    requires (rb_old as (void *) as (struct sized_node *))->rb.rb_left != 0 or left.value == 0;
    requires (rb_old as (void *) as (struct sized_node *))->rb.rb_left != rb_old;
    requires (rb_old as (void *) as (struct sized_node *))->rb.rb_left == 0 or separate(memory((rb_old as (void *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (void *) as (struct sized_node *))->rb.rb_left as (void *) as (struct sized_node *))->size));
    requires (rb_old as (void *) as (struct sized_node *))->rb.rb_left == 0 or separate(memory((rb_old as (void *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (void *) as (struct sized_node *))->rb.rb_left as (void *) as (struct sized_node *))->size));
    requires (rb_old as (void *) as (struct sized_node *))->rb.rb_right != 0 or right.value == 0;
    requires (rb_old as (void *) as (struct sized_node *))->rb.rb_right != rb_old;
    requires (rb_old as (void *) as (struct sized_node *))->rb.rb_right == 0 or separate(memory((rb_old as (void *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (void *) as (struct sized_node *))->rb.rb_right as (void *) as (struct sized_node *))->size));
    requires (rb_old as (void *) as (struct sized_node *))->rb.rb_right == 0 or separate(memory((rb_old as (void *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (void *) as (struct sized_node *))->rb.rb_right as (void *) as (struct sized_node *))->size));
    requires separate(memory((rb_old as (void *) as (struct sized_node *))->rb.rb_left), memory((rb_new as (void *) as (struct sized_node *))->size));
    requires separate(memory((rb_old as (void *) as (struct sized_node *))->rb.rb_right), memory((rb_new as (void *) as (struct sized_node *))->size));
    requires 0 <= left.value;
    requires 0 <= right.value;
    requires right.value <= 2147483646;
    requires left.value <= 2147483646 - right.value;
    ensures target.value == old(source.value);
    ensures source.value == 1 + old(left.value) + old(right.value);
    ensures left.value == old(left.value);
    ensures right.value == old(right.value);
    ensures structure.model == old(structure.model);
}

theorem sized_rotate_preserves_structure()
executes sized_rotate(struct rb_node* rb_old, struct rb_node* rb_new) {
    ensures RotateSizedStructure(&sized_rotate) as {
        structure: structure, source: source, target: target, left: left, right: right
    } by {
        // The callee's arithmetic guarantees are guarded by definedness.
        apply(size_sum_defined(left.value, right.value));
        // Expose each live child's separation facts before applying the call.
        // A null child contributes no metadata range to its write footprint.
        if (rb_old as (void *) as (struct sized_node *))->rb.rb_left != 0 {
            if (rb_old as (void *) as (struct sized_node *))->rb.rb_right != 0 {
                have separate(memory((rb_old as (void *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (void *) as (struct sized_node *))->rb.rb_left as (void *) as (struct sized_node *))->size)) by {
                    cases {
                        (rb_old as (void *) as (struct sized_node *))->rb.rb_left == 0 => { contradiction((rb_old as (void *) as (struct sized_node *))->rb.rb_left == 0); }
                        separate(memory((rb_old as (void *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (void *) as (struct sized_node *))->rb.rb_left as (void *) as (struct sized_node *))->size)) => { assumption(); }
                    }
                }
                have separate(memory((rb_old as (void *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (void *) as (struct sized_node *))->rb.rb_left as (void *) as (struct sized_node *))->size)) by {
                    cases {
                        (rb_old as (void *) as (struct sized_node *))->rb.rb_left == 0 => { contradiction((rb_old as (void *) as (struct sized_node *))->rb.rb_left == 0); }
                        separate(memory((rb_old as (void *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (void *) as (struct sized_node *))->rb.rb_left as (void *) as (struct sized_node *))->size)) => { assumption(); }
                    }
                }
                have separate(memory((rb_old as (void *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (void *) as (struct sized_node *))->rb.rb_right as (void *) as (struct sized_node *))->size)) by {
                    cases {
                        (rb_old as (void *) as (struct sized_node *))->rb.rb_right == 0 => { contradiction((rb_old as (void *) as (struct sized_node *))->rb.rb_right == 0); }
                        separate(memory((rb_old as (void *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (void *) as (struct sized_node *))->rb.rb_right as (void *) as (struct sized_node *))->size)) => { assumption(); }
                    }
                }
                have separate(memory((rb_old as (void *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (void *) as (struct sized_node *))->rb.rb_right as (void *) as (struct sized_node *))->size)) by {
                    cases {
                        (rb_old as (void *) as (struct sized_node *))->rb.rb_right == 0 => { contradiction((rb_old as (void *) as (struct sized_node *))->rb.rb_right == 0); }
                        separate(memory((rb_old as (void *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (void *) as (struct sized_node *))->rb.rb_right as (void *) as (struct sized_node *))->size)) => { assumption(); }
                    }
                }
                step(sized_rotate, {
                    source: source, target: target, left: left, right: right
                });
                solve();
            } else {
                have separate(memory((rb_old as (void *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (void *) as (struct sized_node *))->rb.rb_left as (void *) as (struct sized_node *))->size)) by {
                    cases {
                        (rb_old as (void *) as (struct sized_node *))->rb.rb_left == 0 => { contradiction((rb_old as (void *) as (struct sized_node *))->rb.rb_left == 0); }
                        separate(memory((rb_old as (void *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (void *) as (struct sized_node *))->rb.rb_left as (void *) as (struct sized_node *))->size)) => { assumption(); }
                    }
                }
                have separate(memory((rb_old as (void *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (void *) as (struct sized_node *))->rb.rb_left as (void *) as (struct sized_node *))->size)) by {
                    cases {
                        (rb_old as (void *) as (struct sized_node *))->rb.rb_left == 0 => { contradiction((rb_old as (void *) as (struct sized_node *))->rb.rb_left == 0); }
                        separate(memory((rb_old as (void *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (void *) as (struct sized_node *))->rb.rb_left as (void *) as (struct sized_node *))->size)) => { assumption(); }
                    }
                }
                step(sized_rotate, {
                    source: source, target: target, left: left, right: right
                });
                solve();
            }
        } else {
            if (rb_old as (void *) as (struct sized_node *))->rb.rb_right != 0 {
                have separate(memory((rb_old as (void *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (void *) as (struct sized_node *))->rb.rb_right as (void *) as (struct sized_node *))->size)) by {
                    cases {
                        (rb_old as (void *) as (struct sized_node *))->rb.rb_right == 0 => { contradiction((rb_old as (void *) as (struct sized_node *))->rb.rb_right == 0); }
                        separate(memory((rb_old as (void *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (void *) as (struct sized_node *))->rb.rb_right as (void *) as (struct sized_node *))->size)) => { assumption(); }
                    }
                }
                have separate(memory((rb_old as (void *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (void *) as (struct sized_node *))->rb.rb_right as (void *) as (struct sized_node *))->size)) by {
                    cases {
                        (rb_old as (void *) as (struct sized_node *))->rb.rb_right == 0 => { contradiction((rb_old as (void *) as (struct sized_node *))->rb.rb_right == 0); }
                        separate(memory((rb_old as (void *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (void *) as (struct sized_node *))->rb.rb_right as (void *) as (struct sized_node *))->size)) => { assumption(); }
                    }
                }
                step(sized_rotate, {
                    source: source, target: target, left: left, right: right
                });
                solve();
            } else {
                step(sized_rotate, {
                    source: source, target: target, left: left, right: right
                });
                solve();
            }
        }
    }
}
