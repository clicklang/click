verifying "rbtree_size_rotate.c";
verifying "rbtree_size_compute.c";
verifying "rbtree_size_copy.c";
import "rbtree_size_compute.click";

void sized_rotate(struct rb_node* rb_old, struct rb_node* rb_new) {
    requires rb_old != 0;
    requires rb_new != 0;
    requires rb_old != rb_new;
    views ((struct sized_node*)(void*)rb_old)->rb.rb_left;
    views ((struct sized_node*)(void*)rb_old)->rb.rb_right;
    owns source: size_metadata(rb_old);
    owns target: size_metadata(rb_new);
    owns left: optional_size(((struct sized_node*)(void*)rb_old)->rb.rb_left);
    owns right: optional_size(((struct sized_node*)(void*)rb_old)->rb.rb_right);
    requires ((struct sized_node*)(void*)rb_old)->rb.rb_left != 0 or left.value == 0;
    requires ((struct sized_node*)(void*)rb_old)->rb.rb_left != rb_old;
    requires ((struct sized_node*)(void*)rb_old)->rb.rb_left == 0 or separate(memory(((struct sized_node*)(void*)rb_old)->rb.rb_left), memory(((struct sized_node*)(void*)((struct sized_node*)(void*)rb_old)->rb.rb_left)->size));
    requires ((struct sized_node*)(void*)rb_old)->rb.rb_left == 0 or separate(memory(((struct sized_node*)(void*)rb_old)->rb.rb_right), memory(((struct sized_node*)(void*)((struct sized_node*)(void*)rb_old)->rb.rb_left)->size));
    requires ((struct sized_node*)(void*)rb_old)->rb.rb_right != 0 or right.value == 0;
    requires ((struct sized_node*)(void*)rb_old)->rb.rb_right != rb_old;
    requires ((struct sized_node*)(void*)rb_old)->rb.rb_right == 0 or separate(memory(((struct sized_node*)(void*)rb_old)->rb.rb_left), memory(((struct sized_node*)(void*)((struct sized_node*)(void*)rb_old)->rb.rb_right)->size));
    requires ((struct sized_node*)(void*)rb_old)->rb.rb_right == 0 or separate(memory(((struct sized_node*)(void*)rb_old)->rb.rb_right), memory(((struct sized_node*)(void*)((struct sized_node*)(void*)rb_old)->rb.rb_right)->size));
    requires separate(memory(((struct sized_node*)(void*)rb_old)->rb.rb_left), memory(((struct sized_node*)(void*)rb_new)->size));
    requires separate(memory(((struct sized_node*)(void*)rb_old)->rb.rb_right), memory(((struct sized_node*)(void*)rb_new)->size));
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
    // Both container_of expansions and the metadata copy.
    execute_until(statement(15));
    fold(source);
    let target = fold(size_metadata(rb_new), { value: old(source.value) });
    apply(size_sum_defined(left.value, right.value));
        if ((struct sized_node*)(void*)rb_old)->rb.rb_left != 0 {
            if ((struct sized_node*)(void*)rb_old)->rb.rb_right != 0 {
                have separate(memory(((struct sized_node*)(void*)rb_old)->rb.rb_left), memory(((struct sized_node*)(void*)((struct sized_node*)(void*)rb_old)->rb.rb_left)->size)) by {
                    cases {
                        ((struct sized_node*)(void*)rb_old)->rb.rb_left == 0 => { contradiction(((struct sized_node*)(void*)rb_old)->rb.rb_left == 0); }
                        separate(memory(((struct sized_node*)(void*)rb_old)->rb.rb_left), memory(((struct sized_node*)(void*)((struct sized_node*)(void*)rb_old)->rb.rb_left)->size)) => { assumption(); }
                    }
                }
                have separate(memory(((struct sized_node*)(void*)rb_old)->rb.rb_right), memory(((struct sized_node*)(void*)((struct sized_node*)(void*)rb_old)->rb.rb_left)->size)) by {
                    cases {
                        ((struct sized_node*)(void*)rb_old)->rb.rb_left == 0 => { contradiction(((struct sized_node*)(void*)rb_old)->rb.rb_left == 0); }
                        separate(memory(((struct sized_node*)(void*)rb_old)->rb.rb_right), memory(((struct sized_node*)(void*)((struct sized_node*)(void*)rb_old)->rb.rb_left)->size)) => { assumption(); }
                    }
                }
                have separate(memory(((struct sized_node*)(void*)rb_old)->rb.rb_left), memory(((struct sized_node*)(void*)((struct sized_node*)(void*)rb_old)->rb.rb_right)->size)) by {
                    cases {
                        ((struct sized_node*)(void*)rb_old)->rb.rb_right == 0 => { contradiction(((struct sized_node*)(void*)rb_old)->rb.rb_right == 0); }
                        separate(memory(((struct sized_node*)(void*)rb_old)->rb.rb_left), memory(((struct sized_node*)(void*)((struct sized_node*)(void*)rb_old)->rb.rb_right)->size)) => { assumption(); }
                    }
                }
                have separate(memory(((struct sized_node*)(void*)rb_old)->rb.rb_right), memory(((struct sized_node*)(void*)((struct sized_node*)(void*)rb_old)->rb.rb_right)->size)) by {
                    cases {
                        ((struct sized_node*)(void*)rb_old)->rb.rb_right == 0 => { contradiction(((struct sized_node*)(void*)rb_old)->rb.rb_right == 0); }
                        separate(memory(((struct sized_node*)(void*)rb_old)->rb.rb_right), memory(((struct sized_node*)(void*)((struct sized_node*)(void*)rb_old)->rb.rb_right)->size)) => { assumption(); }
                    }
                }
                step(compute_size(c(old), 0), { parent: source, left: left, right: right });
                step();
                simp();
            } else {
                have separate(memory(((struct sized_node*)(void*)rb_old)->rb.rb_left), memory(((struct sized_node*)(void*)((struct sized_node*)(void*)rb_old)->rb.rb_left)->size)) by {
                    cases {
                        ((struct sized_node*)(void*)rb_old)->rb.rb_left == 0 => { contradiction(((struct sized_node*)(void*)rb_old)->rb.rb_left == 0); }
                        separate(memory(((struct sized_node*)(void*)rb_old)->rb.rb_left), memory(((struct sized_node*)(void*)((struct sized_node*)(void*)rb_old)->rb.rb_left)->size)) => { assumption(); }
                    }
                }
                have separate(memory(((struct sized_node*)(void*)rb_old)->rb.rb_right), memory(((struct sized_node*)(void*)((struct sized_node*)(void*)rb_old)->rb.rb_left)->size)) by {
                    cases {
                        ((struct sized_node*)(void*)rb_old)->rb.rb_left == 0 => { contradiction(((struct sized_node*)(void*)rb_old)->rb.rb_left == 0); }
                        separate(memory(((struct sized_node*)(void*)rb_old)->rb.rb_right), memory(((struct sized_node*)(void*)((struct sized_node*)(void*)rb_old)->rb.rb_left)->size)) => { assumption(); }
                    }
                }
                step(compute_size(c(old), 0), { parent: source, left: left, right: right });
                step();
                simp();
            }
        } else {
            if ((struct sized_node*)(void*)rb_old)->rb.rb_right != 0 {
                have separate(memory(((struct sized_node*)(void*)rb_old)->rb.rb_left), memory(((struct sized_node*)(void*)((struct sized_node*)(void*)rb_old)->rb.rb_right)->size)) by {
                    cases {
                        ((struct sized_node*)(void*)rb_old)->rb.rb_right == 0 => { contradiction(((struct sized_node*)(void*)rb_old)->rb.rb_right == 0); }
                        separate(memory(((struct sized_node*)(void*)rb_old)->rb.rb_left), memory(((struct sized_node*)(void*)((struct sized_node*)(void*)rb_old)->rb.rb_right)->size)) => { assumption(); }
                    }
                }
                have separate(memory(((struct sized_node*)(void*)rb_old)->rb.rb_right), memory(((struct sized_node*)(void*)((struct sized_node*)(void*)rb_old)->rb.rb_right)->size)) by {
                    cases {
                        ((struct sized_node*)(void*)rb_old)->rb.rb_right == 0 => { contradiction(((struct sized_node*)(void*)rb_old)->rb.rb_right == 0); }
                        separate(memory(((struct sized_node*)(void*)rb_old)->rb.rb_right), memory(((struct sized_node*)(void*)((struct sized_node*)(void*)rb_old)->rb.rb_right)->size)) => { assumption(); }
                    }
                }
                step(compute_size(c(old), 0), { parent: source, left: left, right: right });
                step();
                simp();
            } else {
                step(compute_size(c(old), 0), { parent: source, left: left, right: right });
                step();
                simp();
            }
        }
}

contract void RotateSize(struct rb_node* rb_old, struct rb_node* rb_new) {
    requires rb_old != 0;
    requires rb_new != 0;
    requires rb_old != rb_new;
    views ((struct sized_node*)(void*)rb_old)->rb.rb_left;
    views ((struct sized_node*)(void*)rb_old)->rb.rb_right;
    owns source: size_metadata(rb_old);
    owns target: size_metadata(rb_new);
    owns left: optional_size(((struct sized_node*)(void*)rb_old)->rb.rb_left);
    owns right: optional_size(((struct sized_node*)(void*)rb_old)->rb.rb_right);
    requires ((struct sized_node*)(void*)rb_old)->rb.rb_left != 0 or left.value == 0;
    requires ((struct sized_node*)(void*)rb_old)->rb.rb_left != rb_old;
    requires ((struct sized_node*)(void*)rb_old)->rb.rb_left == 0 or separate(memory(((struct sized_node*)(void*)rb_old)->rb.rb_left), memory(((struct sized_node*)(void*)((struct sized_node*)(void*)rb_old)->rb.rb_left)->size));
    requires ((struct sized_node*)(void*)rb_old)->rb.rb_left == 0 or separate(memory(((struct sized_node*)(void*)rb_old)->rb.rb_right), memory(((struct sized_node*)(void*)((struct sized_node*)(void*)rb_old)->rb.rb_left)->size));
    requires ((struct sized_node*)(void*)rb_old)->rb.rb_right != 0 or right.value == 0;
    requires ((struct sized_node*)(void*)rb_old)->rb.rb_right != rb_old;
    requires ((struct sized_node*)(void*)rb_old)->rb.rb_right == 0 or separate(memory(((struct sized_node*)(void*)rb_old)->rb.rb_left), memory(((struct sized_node*)(void*)((struct sized_node*)(void*)rb_old)->rb.rb_right)->size));
    requires ((struct sized_node*)(void*)rb_old)->rb.rb_right == 0 or separate(memory(((struct sized_node*)(void*)rb_old)->rb.rb_right), memory(((struct sized_node*)(void*)((struct sized_node*)(void*)rb_old)->rb.rb_right)->size));
    requires separate(memory(((struct sized_node*)(void*)rb_old)->rb.rb_left), memory(((struct sized_node*)(void*)rb_new)->size));
    requires separate(memory(((struct sized_node*)(void*)rb_old)->rb.rb_right), memory(((struct sized_node*)(void*)rb_new)->size));
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
        if ((struct sized_node*)(void*)rb_old)->rb.rb_left != 0 {
            if ((struct sized_node*)(void*)rb_old)->rb.rb_right != 0 {
                have separate(memory(((struct sized_node*)(void*)rb_old)->rb.rb_left), memory(((struct sized_node*)(void*)((struct sized_node*)(void*)rb_old)->rb.rb_left)->size)) by {
                    cases {
                        ((struct sized_node*)(void*)rb_old)->rb.rb_left == 0 => { contradiction(((struct sized_node*)(void*)rb_old)->rb.rb_left == 0); }
                        separate(memory(((struct sized_node*)(void*)rb_old)->rb.rb_left), memory(((struct sized_node*)(void*)((struct sized_node*)(void*)rb_old)->rb.rb_left)->size)) => { assumption(); }
                    }
                }
                have separate(memory(((struct sized_node*)(void*)rb_old)->rb.rb_right), memory(((struct sized_node*)(void*)((struct sized_node*)(void*)rb_old)->rb.rb_left)->size)) by {
                    cases {
                        ((struct sized_node*)(void*)rb_old)->rb.rb_left == 0 => { contradiction(((struct sized_node*)(void*)rb_old)->rb.rb_left == 0); }
                        separate(memory(((struct sized_node*)(void*)rb_old)->rb.rb_right), memory(((struct sized_node*)(void*)((struct sized_node*)(void*)rb_old)->rb.rb_left)->size)) => { assumption(); }
                    }
                }
                have separate(memory(((struct sized_node*)(void*)rb_old)->rb.rb_left), memory(((struct sized_node*)(void*)((struct sized_node*)(void*)rb_old)->rb.rb_right)->size)) by {
                    cases {
                        ((struct sized_node*)(void*)rb_old)->rb.rb_right == 0 => { contradiction(((struct sized_node*)(void*)rb_old)->rb.rb_right == 0); }
                        separate(memory(((struct sized_node*)(void*)rb_old)->rb.rb_left), memory(((struct sized_node*)(void*)((struct sized_node*)(void*)rb_old)->rb.rb_right)->size)) => { assumption(); }
                    }
                }
                have separate(memory(((struct sized_node*)(void*)rb_old)->rb.rb_right), memory(((struct sized_node*)(void*)((struct sized_node*)(void*)rb_old)->rb.rb_right)->size)) by {
                    cases {
                        ((struct sized_node*)(void*)rb_old)->rb.rb_right == 0 => { contradiction(((struct sized_node*)(void*)rb_old)->rb.rb_right == 0); }
                        separate(memory(((struct sized_node*)(void*)rb_old)->rb.rb_right), memory(((struct sized_node*)(void*)((struct sized_node*)(void*)rb_old)->rb.rb_right)->size)) => { assumption(); }
                    }
                }
                step(sized_rotate(rb_old, rb_new), { source: s, target: t, left: l, right: r });
                simp();
            } else {
                have separate(memory(((struct sized_node*)(void*)rb_old)->rb.rb_left), memory(((struct sized_node*)(void*)((struct sized_node*)(void*)rb_old)->rb.rb_left)->size)) by {
                    cases {
                        ((struct sized_node*)(void*)rb_old)->rb.rb_left == 0 => { contradiction(((struct sized_node*)(void*)rb_old)->rb.rb_left == 0); }
                        separate(memory(((struct sized_node*)(void*)rb_old)->rb.rb_left), memory(((struct sized_node*)(void*)((struct sized_node*)(void*)rb_old)->rb.rb_left)->size)) => { assumption(); }
                    }
                }
                have separate(memory(((struct sized_node*)(void*)rb_old)->rb.rb_right), memory(((struct sized_node*)(void*)((struct sized_node*)(void*)rb_old)->rb.rb_left)->size)) by {
                    cases {
                        ((struct sized_node*)(void*)rb_old)->rb.rb_left == 0 => { contradiction(((struct sized_node*)(void*)rb_old)->rb.rb_left == 0); }
                        separate(memory(((struct sized_node*)(void*)rb_old)->rb.rb_right), memory(((struct sized_node*)(void*)((struct sized_node*)(void*)rb_old)->rb.rb_left)->size)) => { assumption(); }
                    }
                }
                step(sized_rotate(rb_old, rb_new), { source: s, target: t, left: l, right: r });
                simp();
            }
        } else {
            if ((struct sized_node*)(void*)rb_old)->rb.rb_right != 0 {
                have separate(memory(((struct sized_node*)(void*)rb_old)->rb.rb_left), memory(((struct sized_node*)(void*)((struct sized_node*)(void*)rb_old)->rb.rb_right)->size)) by {
                    cases {
                        ((struct sized_node*)(void*)rb_old)->rb.rb_right == 0 => { contradiction(((struct sized_node*)(void*)rb_old)->rb.rb_right == 0); }
                        separate(memory(((struct sized_node*)(void*)rb_old)->rb.rb_left), memory(((struct sized_node*)(void*)((struct sized_node*)(void*)rb_old)->rb.rb_right)->size)) => { assumption(); }
                    }
                }
                have separate(memory(((struct sized_node*)(void*)rb_old)->rb.rb_right), memory(((struct sized_node*)(void*)((struct sized_node*)(void*)rb_old)->rb.rb_right)->size)) by {
                    cases {
                        ((struct sized_node*)(void*)rb_old)->rb.rb_right == 0 => { contradiction(((struct sized_node*)(void*)rb_old)->rb.rb_right == 0); }
                        separate(memory(((struct sized_node*)(void*)rb_old)->rb.rb_right), memory(((struct sized_node*)(void*)((struct sized_node*)(void*)rb_old)->rb.rb_right)->size)) => { assumption(); }
                    }
                }
                step(sized_rotate(rb_old, rb_new), { source: s, target: t, left: l, right: r });
                simp();
            } else {
                step(sized_rotate(rb_old, rb_new), { source: s, target: t, left: l, right: r });
                simp();
            }
        }
    }
}
