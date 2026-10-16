// Recompute the dirty root while preserving the certified child models.
// Stable sums name the folded model without reading consumed metadata.
verifying "rbtree_size_compute.c";
verifying "rbtree_size_copy.c";
import "rbtree_size_model.click";
import "size_arithmetic.click";

resource sized_recompute_at(p: struct rb_node*) {
    field model: SizedTree;
    match model {
        SizedTree::Empty => { fact p == 0; },
        SizedTree::Node(identity, parent, color, value, left_model, right_model) => {
            owns p->__rb_parent_color;
            owns p->rb_left;
            owns p->rb_right;
            owns metadata: size_metadata(p);
            owns left: sized_at(p->rb_left);
            owns right: sized_at(p->rb_right);
            fact metadata.value == value;
            fact left.model == left_model;
            fact right.model == right_model;
            fact p != 0;
            fact p == identity;
            fact p->rb_left != p;
            fact p->rb_right != p;
            fact aligned(p, 8);
            fact aligned(parent, 8);
            fact p->__rb_parent_color == address(parent) + (p->__rb_parent_color & 1);
            fact (p->__rb_parent_color & 1) == color_bit(color);
            fact sized_parent_is(left_model, p) == 1;
            fact sized_parent_is(right_model, p) == 1;
        },
    }
}

contract int32 RecomputeTree(struct sized_node* node, int32 exit) {
    consumes tree: sized_recompute_at((struct rb_node*)(void*)node);
    produces checked: sized_at((struct rb_node*)(void*)node);
    requires node != 0;
    requires 0 <= sized_value(sized_left(tree.model));
    requires 0 <= sized_value(sized_right(tree.model));
    requires sized_value(sized_right(tree.model)) <= 2147483646;
    requires sized_value(sized_left(tree.model)) <= 2147483646 - sized_value(sized_right(tree.model));
    ensures sized_shape(checked.model) == sized_shape(old(tree.model));
    ensures sized_left(checked.model) == sized_left(old(tree.model));
    ensures sized_right(checked.model) == sized_right(old(tree.model));
    ensures sized_counts_valid(checked.model) == 1;
    ensures to_integer(sized_value(checked.model)) == rb_subtree_size(sized_shape(checked.model));
    ensures result == 0 or result == 1;
    ensures result == 0 or sized_value(checked.model) == sized_value(old(tree.model));
}

theorem compute_size_restores_subtree_size()
    executes compute_size(struct sized_node* node, int32 exit) {
    ensures RecomputeTree(&compute_size) as { tree: tree, checked: checked } by {
        match tree.model {
            SizedTree::Empty => { unfold(tree); contradiction(node == 0); },
            SizedTree::Node(identity, parent, color, value, left_model, right_model) => {
                let { metadata: metadata, left: left, right: right } = unfold(tree);
                have sized_left(old(tree.model)) == left_model by {
                    rewrite(old(tree.model) == SizedTree::Node(identity, parent, color, value, left_model, right_model));
                    unfold(sized_left(SizedTree::Node(identity, parent, color, value, left_model, right_model)));
                    normalize();
                }
                have sized_right(old(tree.model)) == right_model by {
                    rewrite(old(tree.model) == SizedTree::Node(identity, parent, color, value, left_model, right_model));
                    unfold(sized_right(SizedTree::Node(identity, parent, color, value, left_model, right_model)));
                    normalize();
                }
                have 0 <= sized_value(left_model) by {
                    rewrite(left_model == sized_left(old(tree.model)));
                    assumption();
                }
                have 0 <= sized_value(right_model) by {
                    rewrite(right_model == sized_right(old(tree.model)));
                    assumption();
                }
                have sized_value(right_model) <= 2147483646 by {
                    rewrite(right_model == sized_right(old(tree.model)));
                    assumption();
                }
                have defined(2147483646 - sized_value(right_model)) by auto();
                have sized_value(left_model) <= 2147483646 - sized_value(right_model) by {
                    rewrite(left_model == sized_left(old(tree.model)));
                    rewrite(right_model == sized_right(old(tree.model)));
                    assumption();
                }
                let { checked: left } = certify_size(node->rb.rb_left, { tree: left });
                let { checked: right } = certify_size(node->rb.rb_right, { tree: right });
                have sized_counts_valid(left_model) == 1 by { rewrite(left_model == left.model); assumption(); }
                have sized_counts_valid(right_model) == 1 by { rewrite(right_model == right.model); assumption(); }
                have to_integer(sized_value(left_model)) == rb_subtree_size(sized_shape(left_model)) by { rewrite(left_model == left.model); assumption(); }
                have to_integer(sized_value(right_model)) == rb_subtree_size(sized_shape(right_model)) by { rewrite(right_model == right.model); assumption(); }
                unfold(sized_left(SizedTree::Node(identity, parent, color, value, left_model, right_model)));
                unfold(sized_right(SizedTree::Node(identity, parent, color, value, left_model, right_model)));
                match left.model {
                    SizedTree::Empty => {
                        unfold(left);
                        unfold(sized_value(SizedTree::Empty));
                        let l = fold(optional_size(node->rb.rb_left), { value: 0 });
                        match right.model {
                            SizedTree::Empty => {
                                unfold(right);
                                unfold(sized_value(SizedTree::Empty));
                                let r = fold(optional_size(node->rb.rb_right), { value: 0 });
                                apply(size_sum_defined(l.value, r.value));
                                apply(size_sum_as_integer(l.value, r.value));
                                mark before_compute;
                                step(compute_size(node, exit), { parent: metadata, left: l, right: r });

                                have metadata.value == 1 + l.value + r.value by { assumption(); }
                                have l.value == 0 by { assumption(); }
                                have r.value == 0 by { assumption(); }
                                have metadata.value == 1 by {
                                    rewrite(metadata.value == 1 + l.value + r.value);
                                    rewrite(l.value == 0);
                                    rewrite(r.value == 0);
                                    normalize();
                                }
                                unfold(l);
                                let left = fold(sized_at(node->rb.rb_left), { model: SizedTree::Empty });
                                unfold(r);
                                let right = fold(sized_at(node->rb.rb_right), { model: SizedTree::Empty });
                                have to_integer(metadata.value) == 1 + to_integer(sized_value(left_model)) + to_integer(sized_value(right_model)) by {
                                    rewrite(metadata.value == 1);
                                    rewrite(left_model == SizedTree::Empty);
                                    rewrite(right_model == SizedTree::Empty);
                                    unfold(sized_value(SizedTree::Empty));
                                    normalize();
                                }
                                have to_integer(1) == 1 + to_integer(sized_value(left_model)) + to_integer(sized_value(right_model)) by {
                                    rewrite(left_model == SizedTree::Empty);
                                    rewrite(right_model == SizedTree::Empty);
                                    unfold(sized_value(SizedTree::Empty));
                                    normalize();
                                }
                                have result == 0 or 1 == value by {
                                    cases {
                                        result == 0 => { assumption(); }
                                        at(before_compute, metadata.value) == 1 + at(before_compute, l.value) + at(before_compute, r.value) => { assumption(); }
                                    }
                                }
                                let checked = fold(sized_at((struct rb_node*)(void*)node), { model: SizedTree::Node(identity, parent, color, 1, left_model, right_model) }, { metadata: metadata, left: left, right: right });
                                have sized_counts_valid(checked.model) == 1 by {
                                    rewrite(checked.model == SizedTree::Node(identity, parent, color, 1, left_model, right_model));
                                    unfold(sized_counts_valid(SizedTree::Node(identity, parent, color, 1, left_model, right_model)));
                                    normalize() using {
                                        to_integer(1) == 1 + to_integer(sized_value(left_model)) + to_integer(sized_value(right_model));
                                        sized_counts_valid(left_model) == 1;
                                        sized_counts_valid(right_model) == 1;
                                    };
                                }
                                have result == 0 or sized_value(checked.model) == sized_value(old(tree.model)) by {
                                    rewrite(checked.model == SizedTree::Node(identity, parent, color, 1, left_model, right_model));
                                    rewrite(old(tree.model) == SizedTree::Node(identity, parent, color, value, left_model, right_model));
                                    unfold(sized_value(SizedTree::Node(identity, parent, color, 1, left_model, right_model)));
                                    unfold(sized_value(SizedTree::Node(identity, parent, color, value, left_model, right_model)));
                                    assumption();
                                }
                                have sized_shape(checked.model) == sized_shape(old(tree.model)) by {
                                    rewrite(checked.model == SizedTree::Node(identity, parent, color, 1, left_model, right_model));
                                    rewrite(old(tree.model) == SizedTree::Node(identity, parent, color, value, left_model, right_model));
                                    unfold(sized_shape(SizedTree::Node(identity, parent, color, 1, left_model, right_model)));
                                    unfold(sized_shape(SizedTree::Node(identity, parent, color, value, left_model, right_model)));
                                    normalize();
                                }
                                have to_integer(sized_value(checked.model)) == rb_subtree_size(sized_shape(checked.model)) by {
                                    rewrite(checked.model == SizedTree::Node(identity, parent, color, 1, left_model, right_model));
                                    unfold(sized_value(SizedTree::Node(identity, parent, color, 1, left_model, right_model)));
                                    unfold(sized_shape(SizedTree::Node(identity, parent, color, 1, left_model, right_model)));
                                    unfold(rb_subtree_size(RbTree::Node(identity, parent, color, sized_shape(left_model), sized_shape(right_model))));
                                    arithmetic() using {
                                        to_integer(1) == 1 + to_integer(sized_value(left_model)) + to_integer(sized_value(right_model));
                                        to_integer(sized_value(left_model)) == rb_subtree_size(sized_shape(left_model));
                                        to_integer(sized_value(right_model)) == rb_subtree_size(sized_shape(right_model));
                                    };
                                }
                                simp();
                            },
                            SizedTree::Node(rid, rp, rc, rv, rl, rr) => {
                                let { metadata: rm, left: rleft, right: rright } = unfold(right);
                                unfold(rm);
                                unfold(sized_value(SizedTree::Node(rid, rp, rc, rv, rl, rr)));
                                let r = fold(optional_size(node->rb.rb_right), { value: rv });
                                apply(size_sum_defined(l.value, r.value));
                                apply(size_sum_as_integer(l.value, r.value));
                                child_size_separation(node, node->rb.rb_right, { metadata: r });
                                mark before_compute;
                                step(compute_size(node, exit), { parent: metadata, left: l, right: r });

                                have l.value == 0 by { assumption(); }
                                have r.value == rv by { assumption(); }
                                have metadata.value == 1 + l.value + r.value by { assumption(); }
                                have metadata.value == 1 + rv by {
                                    rewrite(metadata.value == 1 + l.value + r.value);
                                    rewrite(l.value == 0);
                                    rewrite(r.value == rv);
                                    normalize();
                                }
                                have to_integer(1 + rv) == 1 + to_integer(sized_value(left_model)) + to_integer(sized_value(right_model)) by {
                                    rewrite(left_model == SizedTree::Empty);
                                    unfold(sized_value(SizedTree::Empty));
                                    rewrite(sized_value(right_model) == rv);
                                    assumption();
                                }
                                unfold(l);
                                let left = fold(sized_at(node->rb.rb_left), { model: SizedTree::Empty });
                                unfold(r);
                                let rm = fold(size_metadata(node->rb.rb_right), { value: rv });
                                let right = fold(sized_at(node->rb.rb_right), { model: SizedTree::Node(rid, rp, rc, rv, rl, rr) }, { metadata: rm, left: rleft, right: rright });
                                have to_integer(metadata.value) == 1 + to_integer(sized_value(left_model)) + to_integer(sized_value(right_model)) by {
                                    rewrite(metadata.value == 1 + rv);
                                    assumption();
                                }
                                have result == 0 or 1 + rv == value by {
                                    cases {
                                        result == 0 => { assumption(); }
                                        at(before_compute, metadata.value) == 1 + at(before_compute, l.value) + at(before_compute, r.value) => { assumption(); }
                                    }
                                }
                                let checked = fold(sized_at((struct rb_node*)(void*)node), { model: SizedTree::Node(identity, parent, color, 1 + rv, left_model, right_model) }, { metadata: metadata, left: left, right: right });
                                have sized_counts_valid(checked.model) == 1 by {
                                    rewrite(checked.model == SizedTree::Node(identity, parent, color, 1 + rv, left_model, right_model));
                                    unfold(sized_counts_valid(SizedTree::Node(identity, parent, color, 1 + rv, left_model, right_model)));
                                    normalize() using {
                                        to_integer(1 + rv) == 1 + to_integer(sized_value(left_model)) + to_integer(sized_value(right_model));
                                        sized_counts_valid(left_model) == 1;
                                        sized_counts_valid(right_model) == 1;
                                    };
                                }
                                have result == 0 or sized_value(checked.model) == sized_value(old(tree.model)) by {
                                    rewrite(checked.model == SizedTree::Node(identity, parent, color, 1 + rv, left_model, right_model));
                                    rewrite(old(tree.model) == SizedTree::Node(identity, parent, color, value, left_model, right_model));
                                    unfold(sized_value(SizedTree::Node(identity, parent, color, 1 + rv, left_model, right_model)));
                                    unfold(sized_value(SizedTree::Node(identity, parent, color, value, left_model, right_model)));
                                    assumption();
                                }
                                have sized_shape(checked.model) == sized_shape(old(tree.model)) by {
                                    rewrite(checked.model == SizedTree::Node(identity, parent, color, 1 + rv, left_model, right_model));
                                    rewrite(old(tree.model) == SizedTree::Node(identity, parent, color, value, left_model, right_model));
                                    unfold(sized_shape(SizedTree::Node(identity, parent, color, 1 + rv, left_model, right_model)));
                                    unfold(sized_shape(SizedTree::Node(identity, parent, color, value, left_model, right_model)));
                                    normalize();
                                }
                                have to_integer(sized_value(checked.model)) == rb_subtree_size(sized_shape(checked.model)) by {
                                    rewrite(checked.model == SizedTree::Node(identity, parent, color, 1 + rv, left_model, right_model));
                                    unfold(sized_value(SizedTree::Node(identity, parent, color, 1 + rv, left_model, right_model)));
                                    unfold(sized_shape(SizedTree::Node(identity, parent, color, 1 + rv, left_model, right_model)));
                                    unfold(rb_subtree_size(RbTree::Node(identity, parent, color, sized_shape(left_model), sized_shape(right_model))));
                                    arithmetic() using {
                                        to_integer(1 + rv) == 1 + to_integer(sized_value(left_model)) + to_integer(sized_value(right_model));
                                        to_integer(sized_value(left_model)) == rb_subtree_size(sized_shape(left_model));
                                        to_integer(sized_value(right_model)) == rb_subtree_size(sized_shape(right_model));
                                    };
                                }
                                simp();
                            },
                        }
                    },
                    SizedTree::Node(lid, lp, lc, lv, ll, lr) => {
                        let { metadata: lm, left: lleft, right: lright } = unfold(left);
                        unfold(lm);
                        unfold(sized_value(SizedTree::Node(lid, lp, lc, lv, ll, lr)));
                        have sized_value(left_model) == lv by {
                            have left_model == SizedTree::Node(lid, lp, lc, lv, ll, lr) by { simp(); }
                            rewrite(left_model == SizedTree::Node(lid, lp, lc, lv, ll, lr));
                            unfold(sized_value(SizedTree::Node(lid, lp, lc, lv, ll, lr)));
                            normalize();
                        }
                        let l = fold(optional_size(node->rb.rb_left), { value: lv });
                        match right.model {
                            SizedTree::Empty => {
                                unfold(right);
                                unfold(sized_value(SizedTree::Empty));
                                let r = fold(optional_size(node->rb.rb_right), { value: 0 });
                                have 0 <= l.value by { simp(); }
                                have 0 <= r.value by { simp(); }
                                have r.value <= 2147483646 by { simp(); }
                                have sized_value(right_model) == r.value by { assumption(); }
                                have sized_value(left_model) == l.value by { assumption(); }
                                have 2147483646 - sized_value(right_model) == 2147483646 - r.value by {
                                    rewrite(sized_value(right_model) == r.value);
                                    normalize();
                                }
                                apply(size_sum_defined(l.value, r.value));
                                apply(size_sum_as_integer(l.value, r.value));
                                child_size_separation(node, node->rb.rb_left, { metadata: l });
                                mark before_compute;
                                step(compute_size(node, exit), { parent: metadata, left: l, right: r });

                                have l.value == lv by { assumption(); }
                                have r.value == 0 by { assumption(); }
                                have metadata.value == 1 + lv by { assumption(); }
                                unfold(l);
                                let lm = fold(size_metadata(node->rb.rb_left), { value: lv });
                                let left = fold(sized_at(node->rb.rb_left), { model: SizedTree::Node(lid, lp, lc, lv, ll, lr) }, { metadata: lm, left: lleft, right: lright });
                                unfold(r);
                                let right = fold(sized_at(node->rb.rb_right), { model: SizedTree::Empty });
                                have to_integer(1 + lv) == 1 + to_integer(sized_value(left_model)) + to_integer(sized_value(right_model)) by {
                                    rewrite(left_model == SizedTree::Node(lid, lp, lc, lv, ll, lr));
                                    unfold(sized_value(SizedTree::Node(lid, lp, lc, lv, ll, lr)));
                                    rewrite(right_model == SizedTree::Empty);
                                    unfold(sized_value(SizedTree::Empty));
                                    normalize();
                                    assumption();
                                }
                                have to_integer(metadata.value) == 1 + to_integer(sized_value(left_model)) + to_integer(sized_value(right_model)) by {
                                    rewrite(metadata.value == 1 + lv);
                                    assumption();
                                }
                                have result == 0 or 1 + lv == value by {
                                    cases {
                                        result == 0 => { assumption(); }
                                        at(before_compute, metadata.value) == 1 + at(before_compute, l.value) + at(before_compute, r.value) => { assumption(); }
                                    }
                                }
                                let checked = fold(sized_at((struct rb_node*)(void*)node), { model: SizedTree::Node(identity, parent, color, 1 + lv, left_model, right_model) }, { metadata: metadata, left: left, right: right });
                                have sized_counts_valid(checked.model) == 1 by {
                                    rewrite(checked.model == SizedTree::Node(identity, parent, color, 1 + lv, left_model, right_model));
                                    unfold(sized_counts_valid(SizedTree::Node(identity, parent, color, 1 + lv, left_model, right_model)));
                                    normalize() using {
                                        to_integer(1 + lv) == 1 + to_integer(sized_value(left_model)) + to_integer(sized_value(right_model));
                                        sized_counts_valid(left_model) == 1;
                                        sized_counts_valid(right_model) == 1;
                                    };
                                }
                                have result == 0 or sized_value(checked.model) == sized_value(old(tree.model)) by {
                                    rewrite(checked.model == SizedTree::Node(identity, parent, color, 1 + lv, left_model, right_model));
                                    rewrite(old(tree.model) == SizedTree::Node(identity, parent, color, value, left_model, right_model));
                                    unfold(sized_value(SizedTree::Node(identity, parent, color, 1 + lv, left_model, right_model)));
                                    unfold(sized_value(SizedTree::Node(identity, parent, color, value, left_model, right_model)));
                                    assumption();
                                }
                                have sized_shape(checked.model) == sized_shape(old(tree.model)) by {
                                    rewrite(checked.model == SizedTree::Node(identity, parent, color, 1 + lv, left_model, right_model));
                                    rewrite(old(tree.model) == SizedTree::Node(identity, parent, color, value, left_model, right_model));
                                    unfold(sized_shape(SizedTree::Node(identity, parent, color, 1 + lv, left_model, right_model)));
                                    unfold(sized_shape(SizedTree::Node(identity, parent, color, value, left_model, right_model)));
                                    normalize();
                                }
                                have to_integer(sized_value(checked.model)) == rb_subtree_size(sized_shape(checked.model)) by {
                                    rewrite(checked.model == SizedTree::Node(identity, parent, color, 1 + lv, left_model, right_model));
                                    unfold(sized_value(SizedTree::Node(identity, parent, color, 1 + lv, left_model, right_model)));
                                    unfold(sized_shape(SizedTree::Node(identity, parent, color, 1 + lv, left_model, right_model)));
                                    unfold(rb_subtree_size(RbTree::Node(identity, parent, color, sized_shape(left_model), sized_shape(right_model))));
                                    arithmetic() using {
                                        to_integer(1 + lv) == 1 + to_integer(sized_value(left_model)) + to_integer(sized_value(right_model));
                                        to_integer(sized_value(left_model)) == rb_subtree_size(sized_shape(left_model));
                                        to_integer(sized_value(right_model)) == rb_subtree_size(sized_shape(right_model));
                                    };
                                }
                                simp();
                            },
                            SizedTree::Node(rid, rp, rc, rv, rl, rr) => {
                                let { metadata: rm, left: rleft, right: rright } = unfold(right);
                                unfold(rm);
                                unfold(sized_value(SizedTree::Node(rid, rp, rc, rv, rl, rr)));
                                have sized_value(right_model) == rv by {
                                    have right_model == SizedTree::Node(rid, rp, rc, rv, rl, rr) by { simp(); }
                                    rewrite(right_model == SizedTree::Node(rid, rp, rc, rv, rl, rr));
                                    unfold(sized_value(SizedTree::Node(rid, rp, rc, rv, rl, rr)));
                                    normalize();
                                }
                                let r = fold(optional_size(node->rb.rb_right), { value: rv });
                                apply(size_sum_defined(l.value, r.value));
                                apply(size_sum_as_integer(l.value, r.value));
                                child_size_separation(node, node->rb.rb_left, { metadata: l });
                                child_size_separation(node, node->rb.rb_right, { metadata: r });
                                mark before_compute;
                                step(compute_size(node, exit), { parent: metadata, left: l, right: r });

                                have l.value == lv by { assumption(); }
                                have r.value == rv by { assumption(); }
                                have metadata.value == 1 + l.value + r.value by { assumption(); }
                                have metadata.value == 1 + lv + rv by {
                                    rewrite(metadata.value == 1 + l.value + r.value);
                                    rewrite(l.value == lv);
                                    rewrite(r.value == rv);
                                    normalize();
                                }
                                unfold(l);
                                let lm = fold(size_metadata(node->rb.rb_left), { value: lv });
                                let left = fold(sized_at(node->rb.rb_left), { model: SizedTree::Node(lid, lp, lc, lv, ll, lr) }, { metadata: lm, left: lleft, right: lright });
                                unfold(r);
                                let rm = fold(size_metadata(node->rb.rb_right), { value: rv });
                                let right = fold(sized_at(node->rb.rb_right), { model: SizedTree::Node(rid, rp, rc, rv, rl, rr) }, { metadata: rm, left: rleft, right: rright });
                                have to_integer(1 + lv + rv) == 1 + to_integer(sized_value(left_model)) + to_integer(sized_value(right_model)) by {
                                    rewrite(left_model == SizedTree::Node(lid, lp, lc, lv, ll, lr));
                                    unfold(sized_value(SizedTree::Node(lid, lp, lc, lv, ll, lr)));
                                    rewrite(right_model == SizedTree::Node(rid, rp, rc, rv, rl, rr));
                                    unfold(sized_value(SizedTree::Node(rid, rp, rc, rv, rl, rr)));
                                    normalize();
                                    assumption();
                                }
                                have to_integer(metadata.value) == 1 + to_integer(sized_value(left_model)) + to_integer(sized_value(right_model)) by {
                                    rewrite(metadata.value == 1 + lv + rv);
                                    assumption();
                                }
                                have result == 0 or 1 + lv + rv == value by {
                                    cases {
                                        result == 0 => { assumption(); }
                                        at(before_compute, metadata.value) == 1 + at(before_compute, l.value) + at(before_compute, r.value) => { assumption(); }
                                    }
                                }
                                let checked = fold(sized_at((struct rb_node*)(void*)node), { model: SizedTree::Node(identity, parent, color, 1 + lv + rv, left_model, right_model) }, { metadata: metadata, left: left, right: right });
                                have sized_counts_valid(checked.model) == 1 by {
                                    rewrite(checked.model == SizedTree::Node(identity, parent, color, 1 + lv + rv, left_model, right_model));
                                    unfold(sized_counts_valid(SizedTree::Node(identity, parent, color, 1 + lv + rv, left_model, right_model)));
                                    normalize() using {
                                        to_integer(1 + lv + rv) == 1 + to_integer(sized_value(left_model)) + to_integer(sized_value(right_model));
                                        sized_counts_valid(left_model) == 1;
                                        sized_counts_valid(right_model) == 1;
                                    };
                                }
                                have result == 0 or sized_value(checked.model) == sized_value(old(tree.model)) by {
                                    rewrite(checked.model == SizedTree::Node(identity, parent, color, 1 + lv + rv, left_model, right_model));
                                    rewrite(old(tree.model) == SizedTree::Node(identity, parent, color, value, left_model, right_model));
                                    unfold(sized_value(SizedTree::Node(identity, parent, color, 1 + lv + rv, left_model, right_model)));
                                    unfold(sized_value(SizedTree::Node(identity, parent, color, value, left_model, right_model)));
                                    assumption();
                                }
                                have sized_shape(checked.model) == sized_shape(old(tree.model)) by {
                                    rewrite(checked.model == SizedTree::Node(identity, parent, color, 1 + lv + rv, left_model, right_model));
                                    rewrite(old(tree.model) == SizedTree::Node(identity, parent, color, value, left_model, right_model));
                                    unfold(sized_shape(SizedTree::Node(identity, parent, color, 1 + lv + rv, left_model, right_model)));
                                    unfold(sized_shape(SizedTree::Node(identity, parent, color, value, left_model, right_model)));
                                    normalize();
                                }
                                have to_integer(sized_value(checked.model)) == rb_subtree_size(sized_shape(checked.model)) by {
                                    rewrite(checked.model == SizedTree::Node(identity, parent, color, 1 + lv + rv, left_model, right_model));
                                    unfold(sized_value(SizedTree::Node(identity, parent, color, 1 + lv + rv, left_model, right_model)));
                                    unfold(sized_shape(SizedTree::Node(identity, parent, color, 1 + lv + rv, left_model, right_model)));
                                    unfold(rb_subtree_size(RbTree::Node(identity, parent, color, sized_shape(left_model), sized_shape(right_model))));
                                    arithmetic() using {
                                        to_integer(1 + lv + rv) == 1 + to_integer(sized_value(left_model)) + to_integer(sized_value(right_model));
                                        to_integer(sized_value(left_model)) == rb_subtree_size(sized_shape(left_model));
                                        to_integer(sized_value(right_model)) == rb_subtree_size(sized_shape(right_model));
                                    };
                                }
                                simp();
                            },
                        }
                    },
                }
            },
        }
    }
}
