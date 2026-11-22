verifying "rbtree_size_rotate.c";
verifying "rbtree_size_compute.c";
verifying "rbtree_size_copy.c";
import "rbtree_size_compute.click";

void sized_rotate(struct rb_node* rb_old, struct rb_node* rb_new) {
    requires rb_old != 0;
    requires rb_new != 0;
    requires rb_old != rb_new;
    views (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left;
    views (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right;
    owns source: size_metadata(rb_old);
    owns target: size_metadata(rb_new);
    owns left: optional_size((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left);
    owns right: optional_size((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right);
    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left != 0 or left.value == 0;
    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left != rb_old;
    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left == 0 or separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (uint8 *) as (struct sized_node *))->size));
    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left == 0 or separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (uint8 *) as (struct sized_node *))->size));
    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right != 0 or right.value == 0;
    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right != rb_old;
    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right == 0 or separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (uint8 *) as (struct sized_node *))->size));
    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right == 0 or separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (uint8 *) as (struct sized_node *))->size));
    requires separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory((rb_new as (uint8 *) as (struct sized_node *))->size));
    requires separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory((rb_new as (uint8 *) as (struct sized_node *))->size));
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
    step_until(statement(2).entry);
    have old->size == old(source.value);
    have separate(memory(old->size), memory(new->size));
    have old->rb.rb_left != rb_old;
    have old->rb.rb_right != rb_old;
    have separate(memory(old->rb.rb_left), memory(new->size));
    have separate(memory(old->rb.rb_right), memory(new->size));
    mark before_copy;
    step() by { solve(); }
    // The layout ranges include padding, while the copy accesses one int32 cell.
    have contains(memory(new->size), memory((&new->size)[0..1])) by normalize();
    have contains(memory(old->size), memory((&old->size)[0..1])) by normalize();
    have separate(memory((&old->size)[0..1]), memory((&new->size)[0..1])) by {
        apply(click::separation::separate_restrict(memory(old->size), memory(new->size), memory((&old->size)[0..1]), memory((&new->size)[0..1]))) using {
            separate(memory(old->size), memory(new->size));
            contains(memory(old->size), memory((&old->size)[0..1]));
            contains(memory(new->size), memory((&new->size)[0..1]));
        };
    }
    have separate(statement(2).footprint, memory((&old->size)[0..1])) by {
        solve() using { separate(memory((&old->size)[0..1]), memory((&new->size)[0..1])); };
    }
    have old->size == at(before_copy, old->size) by {
        preserve(memory((&old->size)[0..1]), statement(2));
    }
    have old->size == old(source.value) by {
        rewrite(old->size, at(before_copy, old->size)); known();
    }
    have contains(memory(old->rb.rb_left), memory(old->rb.rb_left)) by {
        apply(click::separation::contains_refl(memory(old->rb.rb_left)));
    }
    have separate(memory(old->rb.rb_left), memory((&new->size)[0..1])) by {
        apply(click::separation::separate_restrict(memory(old->rb.rb_left), memory(new->size), memory(old->rb.rb_left), memory((&new->size)[0..1]))) using {
            separate(memory(old->rb.rb_left), memory(new->size));
            contains(memory(old->rb.rb_left), memory(old->rb.rb_left));
            contains(memory(new->size), memory((&new->size)[0..1]));
        };
    }
    have separate(statement(2).footprint, memory(old->rb.rb_left)) by {
        solve() using { separate(memory(old->rb.rb_left), memory((&new->size)[0..1])); };
    }
    have old->rb.rb_left == at(before_copy, old->rb.rb_left) by {
        preserve(memory(old->rb.rb_left), statement(2));
    }
    have old->rb.rb_left != rb_old by {
        rewrite(old->rb.rb_left, at(before_copy, old->rb.rb_left)); known();
    }
    have contains(memory(old->rb.rb_right), memory(old->rb.rb_right)) by {
        apply(click::separation::contains_refl(memory(old->rb.rb_right)));
    }
    have separate(memory(old->rb.rb_right), memory((&new->size)[0..1])) by {
        apply(click::separation::separate_restrict(memory(old->rb.rb_right), memory(new->size), memory(old->rb.rb_right), memory((&new->size)[0..1]))) using {
            separate(memory(old->rb.rb_right), memory(new->size));
            contains(memory(old->rb.rb_right), memory(old->rb.rb_right));
            contains(memory(new->size), memory((&new->size)[0..1]));
        };
    }
    have separate(statement(2).footprint, memory(old->rb.rb_right)) by {
        solve() using { separate(memory(old->rb.rb_right), memory((&new->size)[0..1])); };
    }
    have old->rb.rb_right == at(before_copy, old->rb.rb_right) by {
        preserve(memory(old->rb.rb_right), statement(2));
    }
    have old->rb.rb_right != rb_old by {
        rewrite(old->rb.rb_right, at(before_copy, old->rb.rb_right)); known();
    }
    have old as (uint8 *) as (struct rb_node *) == rb_old;
    have old->rb.rb_left != old as (uint8 *) as (struct rb_node *) by {
        normalize() using {
            old->rb.rb_left != rb_old;
            old as (uint8 *) as (struct rb_node *) == rb_old;
        };
    }
    have old->rb.rb_right != old as (uint8 *) as (struct rb_node *) by {
        normalize() using {
            old->rb.rb_right != rb_old;
            old as (uint8 *) as (struct rb_node *) == rb_old;
        };
    }
    fold(source);
    let target = fold(size_metadata(rb_new), { value: old(source.value) });
    apply(size_sum_defined(left.value, right.value));
        if (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left != 0 {
            if (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right != 0 {
                have separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) by {
                    cases {
                        (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left == 0 => { contradiction((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left == 0); }
                        separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) => { known(); }
                    }
                }
                have separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) by {
                    cases {
                        (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left == 0 => { contradiction((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left == 0); }
                        separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) => { known(); }
                    }
                }
                have separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) by {
                    cases {
                        (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right == 0 => { contradiction((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right == 0); }
                        separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) => { known(); }
                    }
                }
                have separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) by {
                    cases {
                        (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right == 0 => { contradiction((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right == 0); }
                        separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) => { known(); }
                    }
                }
                step(compute_size, { parent: source, left: left, right: right });
                step();
                solve();
            } else {
                have separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) by {
                    cases {
                        (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left == 0 => { contradiction((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left == 0); }
                        separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) => { known(); }
                    }
                }
                have separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) by {
                    cases {
                        (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left == 0 => { contradiction((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left == 0); }
                        separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) => { known(); }
                    }
                }
                step(compute_size, { parent: source, left: left, right: right });
                step();
                solve();
            }
        } else {
            if (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right != 0 {
                have separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) by {
                    cases {
                        (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right == 0 => { contradiction((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right == 0); }
                        separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) => { known(); }
                    }
                }
                have separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) by {
                    cases {
                        (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right == 0 => { contradiction((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right == 0); }
                        separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) => { known(); }
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
    views (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left;
    views (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right;
    owns source: size_metadata(rb_old);
    owns target: size_metadata(rb_new);
    owns left: optional_size((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left);
    owns right: optional_size((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right);
    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left != 0 or left.value == 0;
    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left != rb_old;
    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left == 0 or separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (uint8 *) as (struct sized_node *))->size));
    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left == 0 or separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (uint8 *) as (struct sized_node *))->size));
    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right != 0 or right.value == 0;
    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right != rb_old;
    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right == 0 or separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (uint8 *) as (struct sized_node *))->size));
    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right == 0 or separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (uint8 *) as (struct sized_node *))->size));
    requires separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory((rb_new as (uint8 *) as (struct sized_node *))->size));
    requires separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory((rb_new as (uint8 *) as (struct sized_node *))->size));
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
        if (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left != 0 {
            if (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right != 0 {
                have separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) by {
                    cases {
                        (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left == 0 => { contradiction((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left == 0); }
                        separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) => { known(); }
                    }
                }
                have separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) by {
                    cases {
                        (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left == 0 => { contradiction((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left == 0); }
                        separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) => { known(); }
                    }
                }
                have separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) by {
                    cases {
                        (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right == 0 => { contradiction((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right == 0); }
                        separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) => { known(); }
                    }
                }
                have separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) by {
                    cases {
                        (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right == 0 => { contradiction((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right == 0); }
                        separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) => { known(); }
                    }
                }
                step(sized_rotate, { source: s, target: t, left: l, right: r });
                solve();
            } else {
                have separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) by {
                    cases {
                        (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left == 0 => { contradiction((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left == 0); }
                        separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) => { known(); }
                    }
                }
                have separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) by {
                    cases {
                        (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left == 0 => { contradiction((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left == 0); }
                        separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) => { known(); }
                    }
                }
                step(sized_rotate, { source: s, target: t, left: l, right: r });
                solve();
            }
        } else {
            if (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right != 0 {
                have separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) by {
                    cases {
                        (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right == 0 => { contradiction((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right == 0); }
                        separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) => { known(); }
                    }
                }
                have separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) by {
                    cases {
                        (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right == 0 => { contradiction((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right == 0); }
                        separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) => { known(); }
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
