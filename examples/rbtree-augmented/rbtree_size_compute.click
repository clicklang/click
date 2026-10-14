verifying "rbtree_size_compute.c";
verifying "rbtree_size_copy.c";
import "rbtree_size_copy.click";
import "size_arithmetic.click";

resource optional_size(node: struct rb_node*) {
    field value: int32;
    if node != 0 {
        owns ((struct sized_node*)(void*)node)->size;
        fact ((struct sized_node*)(void*)node)->size == value;
    }
}

int32 compute_size(struct sized_node* node, int32 exit) {
    requires node != 0;
    views node->rb.rb_left;
    views node->rb.rb_right;
    owns parent: size_metadata((struct rb_node*)(void*)node);
    owns left: optional_size(node->rb.rb_left);
    owns right: optional_size(node->rb.rb_right);
    requires node->rb.rb_left != 0 or left.value == 0;
    requires node->rb.rb_right != 0 or right.value == 0;
    requires node->rb.rb_left != (struct rb_node*)(void*)node;
    requires node->rb.rb_right != (struct rb_node*)(void*)node;
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
            have old(left.value) <= 2147483646 by {
                arithmetic() using {
                    0 <= old(right.value);
                    old(right.value) <= 2147483646;
                    old(left.value) <= 2147483646 - old(right.value);
                }
            }
            apply(size_sum_defined(old(left.value), old(right.value)));
            execute();
            fold(left);
            fold(right);
            let parent = fold(size_metadata((struct rb_node*)(void*)node), {
                value: 1 + old(left.value) + old(right.value)
            });
            simp();
        } else {
            have old(right.value) == 0 by {
 cases {
 node->rb.rb_right != 0 => { contradiction(node->rb.rb_right == 0); }
 right.value == 0 => { assumption(); }
 }
 }
            unfold(left);
            unfold(right);
            unfold(parent);
            have old(left.value) <= 2147483646 by {
                arithmetic() using {
                    0 <= old(right.value);
                    old(right.value) <= 2147483646;
                    old(left.value) <= 2147483646 - old(right.value);
                }
            }
            apply(size_sum_defined(old(left.value), old(right.value)));
            execute();
            fold(left);
            fold(right);
            let parent = fold(size_metadata((struct rb_node*)(void*)node), {
                value: 1 + old(left.value) + old(right.value)
            });
            simp();
        }
    } else {
        have old(left.value) == 0 by {
 cases {
 node->rb.rb_left != 0 => { contradiction(node->rb.rb_left == 0); }
 left.value == 0 => { assumption(); }
 }
 }
        if node->rb.rb_right != 0 {
            unfold(left);
            unfold(right);
            unfold(parent);
            have old(left.value) <= 2147483646 by {
                arithmetic() using {
                    0 <= old(right.value);
                    old(right.value) <= 2147483646;
                    old(left.value) <= 2147483646 - old(right.value);
                }
            }
            apply(size_sum_defined(old(left.value), old(right.value)));
            execute();
            fold(left);
            fold(right);
            let parent = fold(size_metadata((struct rb_node*)(void*)node), {
                value: 1 + old(left.value) + old(right.value)
            });
            simp();
        } else {
            have old(right.value) == 0 by {
 cases {
 node->rb.rb_right != 0 => { contradiction(node->rb.rb_right == 0); }
 right.value == 0 => { assumption(); }
 }
 }
            unfold(left);
            unfold(right);
            unfold(parent);
            have old(left.value) <= 2147483646 by {
                arithmetic() using {
                    0 <= old(right.value);
                    old(right.value) <= 2147483646;
                    old(left.value) <= 2147483646 - old(right.value);
                }
            }
            apply(size_sum_defined(old(left.value), old(right.value)));
            execute();
            fold(left);
            fold(right);
            let parent = fold(size_metadata((struct rb_node*)(void*)node), {
                value: 1 + old(left.value) + old(right.value)
            });
            simp();
        }
    }
}

contract int32 ComputeSize(struct sized_node* node, int32 exit) {
    requires node != 0;
    views node->rb.rb_left;
    views node->rb.rb_right;
    owns parent: size_metadata((struct rb_node*)(void*)node);
    owns left: optional_size(node->rb.rb_left);
    owns right: optional_size(node->rb.rb_right);
    requires node->rb.rb_left != 0 or left.value == 0;
    requires node->rb.rb_right != 0 or right.value == 0;
    requires node->rb.rb_left != (struct rb_node*)(void*)node;
    requires node->rb.rb_right != (struct rb_node*)(void*)node;
    requires node->rb.rb_left == 0 or separate(memory(node->rb.rb_left), memory(((struct sized_node*)(void*)node->rb.rb_left)->size));
    requires node->rb.rb_left == 0 or separate(memory(node->rb.rb_right), memory(((struct sized_node*)(void*)node->rb.rb_left)->size));
    requires node->rb.rb_right == 0 or separate(memory(node->rb.rb_left), memory(((struct sized_node*)(void*)node->rb.rb_right)->size));
    requires node->rb.rb_right == 0 or separate(memory(node->rb.rb_right), memory(((struct sized_node*)(void*)node->rb.rb_right)->size));
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

theorem compute_size_has_size_contract()
    executes compute_size(struct sized_node* node, int32 exit) {
    ensures ComputeSize(&compute_size) as { parent: p, left: l, right: r } by {
        apply(size_sum_defined(l.value, r.value));
        if node->rb.rb_left != 0 {
            if node->rb.rb_right != 0 {
                have separate(memory(node->rb.rb_left), memory(((struct sized_node*)(void*)node->rb.rb_left)->size)) by {
                    cases {
                        node->rb.rb_left == 0 => { contradiction(node->rb.rb_left == 0); }
                        separate(memory(node->rb.rb_left), memory(((struct sized_node*)(void*)node->rb.rb_left)->size)) => { assumption(); }
                    }
                }
                have separate(memory(node->rb.rb_right), memory(((struct sized_node*)(void*)node->rb.rb_left)->size)) by {
                    cases {
                        node->rb.rb_left == 0 => { contradiction(node->rb.rb_left == 0); }
                        separate(memory(node->rb.rb_right), memory(((struct sized_node*)(void*)node->rb.rb_left)->size)) => { assumption(); }
                    }
                }
                have separate(memory(node->rb.rb_left), memory(((struct sized_node*)(void*)node->rb.rb_right)->size)) by {
                    cases {
                        node->rb.rb_right == 0 => { contradiction(node->rb.rb_right == 0); }
                        separate(memory(node->rb.rb_left), memory(((struct sized_node*)(void*)node->rb.rb_right)->size)) => { assumption(); }
                    }
                }
                have separate(memory(node->rb.rb_right), memory(((struct sized_node*)(void*)node->rb.rb_right)->size)) by {
                    cases {
                        node->rb.rb_right == 0 => { contradiction(node->rb.rb_right == 0); }
                        separate(memory(node->rb.rb_right), memory(((struct sized_node*)(void*)node->rb.rb_right)->size)) => { assumption(); }
                    }
                }
                step(compute_size(node, exit), { parent: p, left: l, right: r });
                simp();
            } else {
                have separate(memory(node->rb.rb_left), memory(((struct sized_node*)(void*)node->rb.rb_left)->size)) by {
                    cases {
                        node->rb.rb_left == 0 => { contradiction(node->rb.rb_left == 0); }
                        separate(memory(node->rb.rb_left), memory(((struct sized_node*)(void*)node->rb.rb_left)->size)) => { assumption(); }
                    }
                }
                have separate(memory(node->rb.rb_right), memory(((struct sized_node*)(void*)node->rb.rb_left)->size)) by {
                    cases {
                        node->rb.rb_left == 0 => { contradiction(node->rb.rb_left == 0); }
                        separate(memory(node->rb.rb_right), memory(((struct sized_node*)(void*)node->rb.rb_left)->size)) => { assumption(); }
                    }
                }
                step(compute_size(node, exit), { parent: p, left: l, right: r });
                simp();
            }
        } else {
            if node->rb.rb_right != 0 {
                have separate(memory(node->rb.rb_left), memory(((struct sized_node*)(void*)node->rb.rb_right)->size)) by {
                    cases {
                        node->rb.rb_right == 0 => { contradiction(node->rb.rb_right == 0); }
                        separate(memory(node->rb.rb_left), memory(((struct sized_node*)(void*)node->rb.rb_right)->size)) => { assumption(); }
                    }
                }
                have separate(memory(node->rb.rb_right), memory(((struct sized_node*)(void*)node->rb.rb_right)->size)) by {
                    cases {
                        node->rb.rb_right == 0 => { contradiction(node->rb.rb_right == 0); }
                        separate(memory(node->rb.rb_right), memory(((struct sized_node*)(void*)node->rb.rb_right)->size)) => { assumption(); }
                    }
                }
                step(compute_size(node, exit), { parent: p, left: l, right: r });
                simp();
            } else {
                step(compute_size(node, exit), { parent: p, left: l, right: r });
                simp();
            }
        }
    }
}


tactic child_size_separation(node: struct sized_node*, child: struct rb_node*) {
    owns node->rb;
    owns metadata: optional_size(child);
    requires child != 0;
    ensures metadata.value == old(metadata.value);
    ensures separate(memory(node->rb.rb_left), memory(((struct sized_node*)(void*)child)->size));
    ensures separate(memory(node->rb.rb_right), memory(((struct sized_node*)(void*)child)->size));
} by {
    unfold(metadata);
    have separate(memory(node->rb.rb_left), memory(((struct sized_node*)(void*)child)->size)) by assumption();
    have separate(memory(node->rb.rb_right), memory(((struct sized_node*)(void*)child)->size)) by assumption();
    fold(metadata);
}
