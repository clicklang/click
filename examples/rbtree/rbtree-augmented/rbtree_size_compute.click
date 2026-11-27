verifying "rbtree_size_compute.c";
verifying "rbtree_size_copy.c";
import "rbtree_size_copy.click";
import "size_arithmetic.click";

resource optional_size(node: struct rb_node*) {
    field value: int32;
    if node != 0 {
        owns (node as (uint8 *) as (struct sized_node *))->size;
        fact (node as (uint8 *) as (struct sized_node *))->size == value;
    }
}

int32 compute_size(struct sized_node* node, int32 exit) {
    requires node != 0;
    requires defined(&node->size);
    views node->rb.rb_left;
    views node->rb.rb_right;
    owns parent: size_metadata(node as (uint8 *) as (struct rb_node *));
    owns left: optional_size(node->rb.rb_left);
    owns right: optional_size(node->rb.rb_right);
    requires node->rb.rb_left != 0 or left.value == 0;
    requires node->rb.rb_right != 0 or right.value == 0;
    requires node->rb.rb_left != node as (uint8 *) as (struct rb_node *);
    requires node->rb.rb_right != node as (uint8 *) as (struct rb_node *);
    requires 0 <= left.value;
    requires 0 <= right.value;
    requires right.value <= 2147483646;
    requires left.value <= 2147483646 - right.value;
    ensures parent.value == 1 + old(left.value) + old(right.value);
    ensures left.value == old(left.value);
    ensures right.value == old(right.value);
    ensures result == 0 or result == 1;
    ensures result == 0 or old(parent.value) == 1 + old(left.value) + old(right.value);
} by {
    if node->rb.rb_left != 0 {
        if node->rb.rb_right != 0 {
            unfold(left);
            unfold(right);
            unfold(parent);
            apply(size_sum_defined(old(left.value), old(right.value)));
            if exit == 0 {
                step_until(function.exit);
                fold(left);
                fold(right);
                let parent = fold(size_metadata(node as (uint8 *) as (struct rb_node *)), {
                    value: 1 + old(left.value) + old(right.value)
                });
                close();
            } else {
                step_until(statement(3).entry);
                if node->size == size {
                    step_until(function.exit);
                    fold(left);
                    fold(right);
                    let parent = fold(size_metadata(node as (uint8 *) as (struct rb_node *)), {
                        value: 1 + old(left.value) + old(right.value)
                    });
                    close();
                } else {
                    step_until(function.exit);
                    fold(left);
                    fold(right);
                    let parent = fold(size_metadata(node as (uint8 *) as (struct rb_node *)), {
                        value: 1 + old(left.value) + old(right.value)
                    });
                    close();
                }
            }
        } else {
            have old(right.value) == 0 by {
 cases {
 node->rb.rb_right != 0 => { close(); }
 right.value == 0 => { close(); }
 }
 }
            unfold(left);
            unfold(right);
            unfold(parent);
            apply(size_sum_defined(old(left.value), old(right.value)));
            if exit == 0 {
                step_until(function.exit);
                fold(left);
                fold(right);
                let parent = fold(size_metadata(node as (uint8 *) as (struct rb_node *)), {
                    value: 1 + old(left.value) + old(right.value)
                });
                close();
            } else {
                step_until(statement(3).entry);
                if node->size == size {
                    step_until(function.exit);
                    fold(left);
                    fold(right);
                    let parent = fold(size_metadata(node as (uint8 *) as (struct rb_node *)), {
                        value: 1 + old(left.value) + old(right.value)
                    });
                    close();
                } else {
                    step_until(function.exit);
                    fold(left);
                    fold(right);
                    let parent = fold(size_metadata(node as (uint8 *) as (struct rb_node *)), {
                        value: 1 + old(left.value) + old(right.value)
                    });
                    close();
                }
            }
        }
    } else {
        have old(left.value) == 0 by {
 cases {
 node->rb.rb_left != 0 => { close(); }
 left.value == 0 => { close(); }
 }
 }
        if node->rb.rb_right != 0 {
            unfold(left);
            unfold(right);
            unfold(parent);
            apply(size_sum_defined(old(left.value), old(right.value)));
            if exit == 0 {
                step_until(function.exit);
                fold(left);
                fold(right);
                let parent = fold(size_metadata(node as (uint8 *) as (struct rb_node *)), {
                    value: 1 + old(left.value) + old(right.value)
                });
                close();
            } else {
                step_until(statement(3).entry);
                if node->size == size {
                    step_until(function.exit);
                    fold(left);
                    fold(right);
                    let parent = fold(size_metadata(node as (uint8 *) as (struct rb_node *)), {
                        value: 1 + old(left.value) + old(right.value)
                    });
                    close();
                } else {
                    step_until(function.exit);
                    fold(left);
                    fold(right);
                    let parent = fold(size_metadata(node as (uint8 *) as (struct rb_node *)), {
                        value: 1 + old(left.value) + old(right.value)
                    });
                    close();
                }
            }
        } else {
            have old(right.value) == 0 by {
 cases {
 node->rb.rb_right != 0 => { close(); }
 right.value == 0 => { close(); }
 }
 }
            unfold(left);
            unfold(right);
            unfold(parent);
            apply(size_sum_defined(old(left.value), old(right.value)));
            if exit == 0 {
                step_until(function.exit);
                fold(left);
                fold(right);
                let parent = fold(size_metadata(node as (uint8 *) as (struct rb_node *)), {
                    value: 1 + old(left.value) + old(right.value)
                });
                close();
            } else {
                step_until(statement(3).entry);
                if node->size == size {
                    step_until(function.exit);
                    fold(left);
                    fold(right);
                    let parent = fold(size_metadata(node as (uint8 *) as (struct rb_node *)), {
                        value: 1 + old(left.value) + old(right.value)
                    });
                    close();
                } else {
                    step_until(function.exit);
                    fold(left);
                    fold(right);
                    let parent = fold(size_metadata(node as (uint8 *) as (struct rb_node *)), {
                        value: 1 + old(left.value) + old(right.value)
                    });
                    close();
                }
            }
        }
    }
}

contract int32 ComputeSize(struct sized_node* node, int32 exit) {
    requires node != 0;
    requires defined(&node->size);
    views node->rb.rb_left;
    views node->rb.rb_right;
    owns parent: size_metadata(node as (uint8 *) as (struct rb_node *));
    owns left: optional_size(node->rb.rb_left);
    owns right: optional_size(node->rb.rb_right);
    requires node->rb.rb_left != 0 or left.value == 0;
    requires node->rb.rb_right != 0 or right.value == 0;
    requires node->rb.rb_left != node as (uint8 *) as (struct rb_node *);
    requires node->rb.rb_right != node as (uint8 *) as (struct rb_node *);
    requires node->rb.rb_left == 0 or separate(memory(node->rb.rb_left), memory((node->rb.rb_left as (uint8 *) as (struct sized_node *))->size));
    requires node->rb.rb_left == 0 or separate(memory(node->rb.rb_right), memory((node->rb.rb_left as (uint8 *) as (struct sized_node *))->size));
    requires node->rb.rb_right == 0 or separate(memory(node->rb.rb_left), memory((node->rb.rb_right as (uint8 *) as (struct sized_node *))->size));
    requires node->rb.rb_right == 0 or separate(memory(node->rb.rb_right), memory((node->rb.rb_right as (uint8 *) as (struct sized_node *))->size));
    requires 0 <= left.value;
    requires 0 <= right.value;
    requires right.value <= 2147483646;
    requires left.value <= 2147483646 - right.value;
    ensures parent.value == 1 + old(left.value) + old(right.value);
    ensures left.value == old(left.value);
    ensures right.value == old(right.value);
    ensures result == 0 or result == 1;
    ensures result == 0 or old(parent.value) == 1 + old(left.value) + old(right.value);
}

// Call effects check the joined view of the two adjacent child links.
theorem separate_size_write_from_child_links(links: int32*, cache: Resource) {
    requires separate(memory(links[2..4]), cache);
    requires separate(memory(links[4..6]), cache);
    ensures separate(cache, memory(links[2..6])) by {
        apply(click::separation::separate_star(memory(links[2..4]), memory(links[4..6]), cache));
        apply(click::separation::contains_joined_ranges(links, 2, 4, 6));
        apply(click::separation::contains_refl(cache));
        apply(click::separation::separate_restrict(
            memory(links[2..4]) * memory(links[4..6]), cache, memory(links[2..6]), cache));
        apply(click::separation::separate_symm(memory(links[2..6]), cache));
    }
}

theorem compute_size_has_size_contract()
    executes compute_size(struct sized_node* node, int32 exit) {
    ensures ComputeSize(&compute_size) as { parent: p, left: l, right: r } by {
        apply(size_sum_defined(l.value, r.value));
        // The cache slot begins after the two child links.
        apply(click::separation::separate_adjacent_ranges(node as (int32 *), 2, 6, 8));
        apply(click::separation::separate_symm(
            memory((node as (int32 *))[2..6]), memory((node as (int32 *))[6..8])));
        if node->rb.rb_left != 0 {
            if node->rb.rb_right != 0 {
                have separate(memory(node->rb.rb_left), memory((node->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) by {
                    cases {
                        node->rb.rb_left == 0 => { close(); }
                        separate(memory(node->rb.rb_left), memory((node->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) => { close(); }
                    }
                }
                have separate(memory(node->rb.rb_right), memory((node->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) by {
                    cases {
                        node->rb.rb_left == 0 => { close(); }
                        separate(memory(node->rb.rb_right), memory((node->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) => { close(); }
                    }
                }
                have separate(memory(node->rb.rb_left), memory((node->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) by {
                    cases {
                        node->rb.rb_right == 0 => { close(); }
                        separate(memory(node->rb.rb_left), memory((node->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) => { close(); }
                    }
                }
                have separate(memory(node->rb.rb_right), memory((node->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) by {
                    cases {
                        node->rb.rb_right == 0 => { close(); }
                        separate(memory(node->rb.rb_right), memory((node->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) => { close(); }
                    }
                }
                apply(separate_size_write_from_child_links(node as (int32 *),
                    memory((node->rb.rb_left as (int32 *))[6..8])));
                apply(separate_size_write_from_child_links(node as (int32 *),
                    memory((node->rb.rb_right as (int32 *))[6..8])));
                step(compute_size, { parent: p, left: l, right: r });
                close();
            } else {
                have separate(memory(node->rb.rb_left), memory((node->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) by {
                    cases {
                        node->rb.rb_left == 0 => { close(); }
                        separate(memory(node->rb.rb_left), memory((node->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) => { close(); }
                    }
                }
                have separate(memory(node->rb.rb_right), memory((node->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) by {
                    cases {
                        node->rb.rb_left == 0 => { close(); }
                        separate(memory(node->rb.rb_right), memory((node->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) => { close(); }
                    }
                }
                apply(separate_size_write_from_child_links(node as (int32 *),
                    memory((node->rb.rb_left as (int32 *))[6..8])));
                step(compute_size, { parent: p, left: l, right: r });
                close();
            }
        } else {
            if node->rb.rb_right != 0 {
                have separate(memory(node->rb.rb_left), memory((node->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) by {
                    cases {
                        node->rb.rb_right == 0 => { close(); }
                        separate(memory(node->rb.rb_left), memory((node->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) => { close(); }
                    }
                }
                have separate(memory(node->rb.rb_right), memory((node->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) by {
                    cases {
                        node->rb.rb_right == 0 => { close(); }
                        separate(memory(node->rb.rb_right), memory((node->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) => { close(); }
                    }
                }
                apply(separate_size_write_from_child_links(node as (int32 *),
                    memory((node->rb.rb_right as (int32 *))[6..8])));
                step(compute_size, { parent: p, left: l, right: r });
                close();
            } else {
                step(compute_size, { parent: p, left: l, right: r });
                close();
            }
        }
    }
}


tactic child_size_separation(node: struct sized_node*, child: struct rb_node*) {
    owns node->rb;
    owns metadata: optional_size(child);
    requires child != 0;
    ensures metadata.value == old(metadata.value);
    ensures separate(memory(node->rb.rb_left), memory((child as (uint8 *) as (struct sized_node *))->size));
    ensures separate(memory(node->rb.rb_right), memory((child as (uint8 *) as (struct sized_node *))->size));
} by {
    unfold(metadata);
    have separate(memory(node->rb.rb_left), memory((child as (uint8 *) as (struct sized_node *))->size)) by close();
    have separate(memory(node->rb.rb_right), memory((child as (uint8 *) as (struct sized_node *))->size)) by close();
    fold(metadata);
}
