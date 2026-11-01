verifying "rbtree_size_rotate.c";
verifying "rbtree_size_compute.c";
verifying "rbtree_size_copy.c";
import "rbtree_size_compute.click";

void sized_rotate(struct rb_node* rb_old, struct rb_node* rb_new) {
    requires rb_old != 0;
    requires rb_new != 0;
    requires rb_old != rb_new;
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
} by {
    unfold(source);
    unfold(target);
    // Both container_of expansions, then the metadata copy.
    step_until(statement(2));
    have old->size == old(source.value);
    have separate(memory(old->size), memory(new->size));
    have old->rb.rb_left != rb_old;
    have old->rb.rb_right != rb_old;
    have separate(memory(old->rb.rb_left), memory(new->size));
    have separate(memory(old->rb.rb_right), memory(new->size));
    mark before_copy;
    step();
    transport(at(before_copy, old->size) == old(source.value),
              old->size == old(source.value)) using {
        at(before_copy, old->size) == old(source.value);
        separate(memory(old->size), memory(new->size));
    };
    transport(at(before_copy, old->rb.rb_left) != rb_old,
              old->rb.rb_left != rb_old) using {
        at(before_copy, old->rb.rb_left) != rb_old;
        separate(memory(old->rb.rb_left), memory(new->size));
    };
    transport(at(before_copy, old->rb.rb_right) != rb_old,
              old->rb.rb_right != rb_old) using {
        at(before_copy, old->rb.rb_right) != rb_old;
        separate(memory(old->rb.rb_right), memory(new->size));
    };
    have old as (void *) as (struct rb_node *) == rb_old;
    have old->rb.rb_left != old as (void *) as (struct rb_node *) by {
        normalize() using {
            old->rb.rb_left != rb_old;
            old as (void *) as (struct rb_node *) == rb_old;
        };
    }
    have old->rb.rb_right != old as (void *) as (struct rb_node *) by {
        normalize() using {
            old->rb.rb_right != rb_old;
            old as (void *) as (struct rb_node *) == rb_old;
        };
    }
    fold(source);
    let target = fold(size_metadata(rb_new), { value: old(source.value) });
    apply(size_sum_defined(left.value, right.value));
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
                step(compute_size, { parent: source, left: left, right: right });
                step();
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
                step(compute_size, { parent: source, left: left, right: right });
                step();
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
                step(compute_size, { parent: source, left: left, right: right });
                step();
                solve();
            } else {
                step(compute_size, { parent: source, left: left, right: right });
                step();
                solve();
            }
        }
}

contract void RotateSize(struct rb_node* rb_old, struct rb_node* rb_new) {
    requires rb_old != 0;
    requires rb_new != 0;
    requires rb_old != rb_new;
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
}

theorem sized_rotate_has_size_contract()
    executes sized_rotate(struct rb_node* rb_old, struct rb_node* rb_new) {
    ensures RotateSize(&sized_rotate) as { source: s, target: t, left: l, right: r } by {
        apply(size_sum_defined(l.value, r.value));
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
                step(sized_rotate, { source: s, target: t, left: l, right: r });
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
                step(sized_rotate, { source: s, target: t, left: l, right: r });
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
                step(sized_rotate, { source: s, target: t, left: l, right: r });
                solve();
            } else {
                step(sized_rotate, { source: s, target: t, left: l, right: r });
                solve();
            }
        }
    }
}
