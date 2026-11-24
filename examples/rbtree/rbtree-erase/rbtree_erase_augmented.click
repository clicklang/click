// One general contract for the unchanged Linux `__rb_erase_augmented`: any
// node of a valid, parent-consistent tree. Each C exit is one arm of a single
// proof, and the outcome resource says which exit was taken.
import click::separation;
verifying "rb_erase.c";
import "rbtree_erase_callbacks.click";
import "rbtree_change_child.click";
import "../rbtree-model/rbtree_spine_resources.click";
import "rbtree_refold_to_root.click";
import "../rbtree-model/rbtree_erase_one_child.click";

resource erase_saved_left(node: struct rb_node*) {
    field child: int32*;
    owns node->rb_left;
    fact node->rb_left == child;
}

resource erase_saved_right(node: struct rb_node*) {
    field child: int32*;
    owns node->rb_right;
    fact node->rb_right == child;
}

resource erase_saved_children(node: struct rb_node*) {
    field left: int32*;
    field right: int32*;
    owns node->rb_left;
    owns node->rb_right;
    fact node->rb_left == left;
    fact node->rb_right == right;
}

resource erase_saved_color(node: struct rb_node*) {
    field color: Color;
    owns node->__rb_parent_color;
    fact (node->__rb_parent_color & 1) == color_bit(color);
}

resource erase_saved_parent(node: struct rb_node*, parent: struct rb_node*) {
    field word: uint64;
    field color: Color;
    owns node->__rb_parent_color;
    fact node->__rb_parent_color == word;
    fact ((node->__rb_parent_color & ~3) as (struct rb_node *)) == parent;
    fact node->__rb_parent_color == address(parent) + (node->__rb_parent_color & 1);
    fact (node->__rb_parent_color & 1) == color_bit(color);
}

// The subtree that replaces the erased node, before any erase-color repair.
function erase_deep_model(tree: RbTree) -> RbTree {
    match tree {
        RbTree::Empty => RbTree::Empty,
        RbTree::Node(node, parent, color, left, right) => rb_successor_splice(erase_minimum_identity(rb_minimum(right)), parent, color, left, right),
    }
}

function erase_child_deep_model(tree: RbTree) -> RbTree {
    match tree {
        RbTree::Empty => RbTree::Empty,
        RbTree::Node(node, parent, color, left, right) => rb_successor_child_splice(erase_minimum_identity(rb_minimum(right)), parent, color, left, right),
    }
}

function erase_deep_context(tree: RbTree, up: Context) -> Context {
    match tree {
        RbTree::Empty => up,
        RbTree::Node(node, parent, color, left, right) => rb_successor_context(erase_minimum_identity(rb_minimum(right)), parent, color, left, right, up),
    }
}

tactic refold_erase_spine(focus: struct rb_node*, anchor: struct rb_node*) {
    consumes c: erase_spine_at(focus, anchor);
    decreases erase_spine_depth(c.model);
    consumes t: rb_at(focus);
    requires rb_parent_consistent(plug(erase_context(c.model), t.model), anchor) == 1;
    produces whole: erase_left_at(anchor);
    ensures whole.model == plug(erase_context(old(c.model)), old(t.model));
} by {
    match c.model {
        EraseSpine::Top => {
            unfold(c);
            let whole = fold(erase_left_at(anchor), { model: t.model, tree: t });
            have plug(Context::Top, old(t.model)) == old(t.model) by {
                unfold(plug(Context::Top, old(t.model))); close();
            }
            have whole.model == plug(erase_context(old(c.model)), old(t.model)) by {
                rewrite(old(c.model), EraseSpine::Top);
                unfold(erase_context(EraseSpine::Top));
                rewrite(plug(Context::Top, old(t.model)), old(t.model)); close();
            }
        },
        EraseSpine::Left(identity, grandparent, color, sibling_model, up_model) => {
            have erase_context(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model))
                == Context::Left(identity, grandparent, color, sibling_model, erase_context(up_model)) by {
                unfold(erase_context(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model))); close();
            }
            have rb_parent_consistent(plug(Context::Left(identity, grandparent, color, sibling_model, erase_context(up_model)), t.model), anchor) == 1 by {
                rewrite(Context::Left(identity, grandparent, color, sibling_model, erase_context(up_model)), erase_context(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model)));
                rewrite(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model), c.model);
                close();
            }
            apply(plug_parent_consistent_ctx(Context::Left(identity, grandparent, color, sibling_model, erase_context(up_model)), t.model, anchor));
            apply(ctx_consistent_left_focus(identity, grandparent, color, sibling_model, erase_context(up_model), t.model, anchor));
            apply(erase_parent_consistent_parent_is(t.model, identity));
            let { sibling: s, up: u } = unfold(c);
            let sub = fold(rb_at(identity), { model: RbTree::Node(identity, grandparent, color, old(t.model), sibling_model), left: t, right: s });
            apply(erase_spine_depth_is_nonnegative(up_model));
            have 0 <= erase_spine_depth(u.model) by {
                rewrite(u.model, up_model);
                close();
            }
            have erase_spine_depth(old(c.model)) == erase_spine_depth(up_model) + 1 by {
                rewrite(old(c.model), EraseSpine::Left(identity, grandparent, color, sibling_model, up_model));
                unfold(erase_spine_depth(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model)));
                close();
            }
            have erase_spine_depth(u.model) < erase_spine_depth(old(c.model)) by {
                rewrite(u.model, up_model);
                close() using { erase_spine_depth(old(c.model)) == erase_spine_depth(up_model) + 1; };
            }
            have plug(Context::Left(identity, grandparent, color, sibling_model, erase_context(up_model)), old(t.model)) == plug(erase_context(up_model), RbTree::Node(identity, grandparent, color, old(t.model), sibling_model)) by {
                unfold(plug(Context::Left(identity, grandparent, color, sibling_model, erase_context(up_model)), old(t.model)));
                close();
            }
            have rb_parent_consistent(plug(erase_context(u.model), sub.model), anchor) == 1 by {
                rewrite(u.model, up_model);
                rewrite(sub.model, RbTree::Node(identity, grandparent, color, old(t.model), sibling_model));
                rewrite(plug(erase_context(up_model), RbTree::Node(identity, grandparent, color, old(t.model), sibling_model)), plug(Context::Left(identity, grandparent, color, sibling_model, erase_context(up_model)), old(t.model)));
                rewrite(Context::Left(identity, grandparent, color, sibling_model, erase_context(up_model)), erase_context(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model)));
                rewrite(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model), old(c.model));
                close();
            }
            let { whole: whole } = refold_erase_spine(identity, anchor, { c: u, t: sub });
            have whole.model == plug(erase_context(old(c.model)), old(t.model)) by {
                rewrite(old(c.model), EraseSpine::Left(identity, grandparent, color, sibling_model, up_model));
                rewrite(erase_context(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model)), Context::Left(identity, grandparent, color, sibling_model, erase_context(up_model)));
                rewrite(plug(Context::Left(identity, grandparent, color, sibling_model, erase_context(up_model)), old(t.model)), plug(erase_context(up_model), RbTree::Node(identity, grandparent, color, old(t.model), sibling_model)));
                close();
            }
        },
    }
}

// A nonempty focus is still the leftmost candidate through every spine frame.
tactic open_erase_spine_link(focus: struct rb_node*, parent: struct rb_node*, anchor: struct rb_node*) {
    consumes c: erase_spine_at(focus, anchor);
    requires parent == erase_spine_parent(c.model, anchor);
    produces parent->rb_left;
    produces frame: erase_spine_frame(parent, anchor);
    ensures parent->rb_left == focus;
    ensures parent != 0;
    ensures frame.model == old(c.model);
} by {
    match c.model {
        EraseSpine::Top => {
            have erase_spine_parent(c.model, anchor) == anchor by {
                rewrite(c.model, EraseSpine::Top);
                unfold(erase_spine_parent(EraseSpine::Top, anchor)); normalize();
            }
            have parent == anchor by { normalize() using { }; }
            unfold(c);
            have parent != 0;
            let frame = fold(erase_spine_frame(parent, anchor), { model: EraseSpine::Top });
            have parent->rb_left == focus;
            have frame.model == old(c.model);
        },
        EraseSpine::Left(identity, grandparent, color, sibling_model, up_model) => {
            have erase_spine_parent(c.model, anchor) == identity by {
                rewrite(c.model, EraseSpine::Left(identity, grandparent, color, sibling_model, up_model));
                unfold(erase_spine_parent(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model), anchor)); normalize();
            }
            have parent == identity by { normalize() using { }; }
            let { sibling: sibling, up: up } = unfold(c);
            let frame = fold(erase_spine_frame(parent, anchor), {
                model: EraseSpine::Left(identity, grandparent, color, sibling_model, up_model),
                sibling: sibling, up: up
            });
        },
    }
}

tactic close_erase_spine_link(focus: struct rb_node*, parent: struct rb_node*, anchor: struct rb_node*) {
    consumes parent->rb_left;
    consumes frame: erase_spine_frame(parent, anchor);
    requires parent->rb_left == focus;
    produces c: erase_spine_at(focus, anchor);
    ensures c.model == old(frame.model);
} by {
    match frame.model {
        EraseSpine::Top => {
            unfold(frame);
            have anchor->rb_left == focus;
            let c = fold(erase_spine_at(focus, anchor), { model: EraseSpine::Top });
            have c.model == old(frame.model);
        },
        EraseSpine::Left(identity, grandparent, color, sibling_model, up_model) => {
            let { sibling: sibling, up: up } = unfold(frame);
            have parent != 0 by { rewrite(parent, identity); close(); }
            have aligned(parent, 8) by { rewrite(parent, identity); close(); }
            have rb_parent_is(sibling_model, parent) == 1 by { rewrite(parent, identity); close(); }
            let c = fold(erase_spine_at(focus, anchor), {
                model: EraseSpine::Left(identity, grandparent, color, sibling_model, up_model),
                sibling: sibling, up: up
            });
        },
    }
}

tactic graft_erase_spine(focus: struct rb_node*, anchor: struct rb_node*, root: struct rb_root*) {
    consumes c: erase_spine_at(focus, anchor);
    consumes base: erase_anchor_frame(anchor, root);
    decreases erase_spine_depth(c.model);
    requires erase_spine_links(c.model, anchor) == 1;
    produces context: ctx_at(focus, root);
    ensures context.model == ctx_concat(erase_context(old(c.model)),
        erase_anchor_context(anchor, old(base.model)));
} by {
    match base.model {
        EraseAnchorFrame::At(ap, ac, ar, au) => {
    have erase_anchor_context(anchor, old(base.model)) == Context::Left(anchor, ap, ac, ar, au) by {
        rewrite(old(base.model), EraseAnchorFrame::At(ap, ac, ar, au));
        unfold(erase_anchor_context(anchor, EraseAnchorFrame::At(ap, ac, ar, au))); close();
    }
    match c.model {
        EraseSpine::Top => {
            unfold(c);
            let { right: right, up: outer_context } = unfold(base);
            let context = fold(ctx_at(focus, root), {
                model: Context::Left(anchor, ap, ac, ar, au),
                sibling: right, up: outer_context
            });
            have context.model == ctx_concat(erase_context(old(c.model)),
                Context::Left(anchor, ap, ac, ar, au)) by {
                rewrite(old(c.model), EraseSpine::Top);
                unfold(erase_context(EraseSpine::Top));
                unfold(ctx_concat(Context::Top, Context::Left(anchor, ap, ac, ar, au)));
                close();
            }
            have context.model == ctx_concat(erase_context(old(c.model)), erase_anchor_context(anchor, old(base.model))) by {
                rewrite(erase_anchor_context(anchor, old(base.model)), Context::Left(anchor, ap, ac, ar, au)); close();
            }
        },
        EraseSpine::Left(identity, grandparent, color, sibling_model, up_model) => {
            unfold(erase_spine_links(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model), anchor));
            have grandparent == erase_spine_parent(up_model, anchor);
            have (if grandparent == erase_spine_parent(up_model, anchor) { erase_spine_links(up_model, anchor) } else { 0 })
                == erase_spine_links(up_model, anchor) by {
                rewrite(grandparent, erase_spine_parent(up_model, anchor));
                close();
            }
            have erase_spine_links(up_model, anchor) == 1 by {
                rewrite(erase_spine_links(up_model, anchor),
                    if grandparent == erase_spine_parent(up_model, anchor) { erase_spine_links(up_model, anchor) } else { 0 });
                rewrite(if grandparent == erase_spine_parent(up_model, anchor) { erase_spine_links(up_model, anchor) } else { 0 },
                    erase_spine_links(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model), anchor));
                close();
            }
            let { sibling: sibling, up: path_tail } = unfold(c);
            apply(erase_spine_depth_is_nonnegative(up_model));
            have erase_spine_depth(old(c.model)) == erase_spine_depth(up_model) + 1 by {
                rewrite(old(c.model), EraseSpine::Left(identity, grandparent, color, sibling_model, up_model));
                unfold(erase_spine_depth(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model))); close();
            }
            have erase_spine_depth(path_tail.model) < erase_spine_depth(old(c.model));
            mark grafting_tail;
            let { context: above } = graft_erase_spine(identity, anchor, root, { c: path_tail, base: base });
            have above.model == ctx_concat(erase_context(at(grafting_tail, path_tail.model)),
                erase_anchor_context(anchor, at(grafting_tail, base.model))) by { close(); }
            have erase_anchor_context(anchor, EraseAnchorFrame::At(ap, ac, ar, au)) == Context::Left(anchor, ap, ac, ar, au);
            have above.model == ctx_concat(erase_context(up_model),
                Context::Left(anchor, ap, ac, ar, au)) by {
                rewrite(up_model, at(grafting_tail, path_tail.model));
                rewrite(Context::Left(anchor, ap, ac, ar, au), erase_anchor_context(anchor, EraseAnchorFrame::At(ap, ac, ar, au)));
                rewrite(EraseAnchorFrame::At(ap, ac, ar, au), at(grafting_tail, base.model)); close();
            }
            apply(erase_spine_context_parent(up_model, anchor, ap, ac, ar, au));
            let context = fold(ctx_at(focus, root), {
                model: Context::Left(identity, grandparent, color, sibling_model,
                    ctx_concat(erase_context(up_model), Context::Left(anchor, ap, ac, ar, au))),
                up: above,
                sibling: sibling
            });
            have context.model == ctx_concat(erase_context(old(c.model)),
                Context::Left(anchor, ap, ac, ar, au)) by {
                rewrite(old(c.model), EraseSpine::Left(identity, grandparent, color, sibling_model, up_model));
                unfold(erase_context(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model)));
                unfold(ctx_concat(Context::Left(identity, grandparent, color, sibling_model, erase_context(up_model)),
                    Context::Left(anchor, ap, ac, ar, au)));
                close();
            }
            have context.model == ctx_concat(erase_context(old(c.model)), erase_anchor_context(anchor, old(base.model)));
        },
    }
        },
    }
}

spec enum EraseOutcome {
    Balanced(RbTree),
    Deficit(Context),
}

// What the unlink hands to `rb_erase`: either the whole tree and a null
// rebalance pointer, or the context of an empty hole at 0 whose repair starts
// at the nonnull `rebalance`.
resource erase_out(root: struct rb_root*, rebalance: struct rb_node*) {
    field model: EraseOutcome;
    match model {
        EraseOutcome::Balanced(t) => {
            owns whole: rb_root_at(root);
            fact whole.model == t;
            fact rebalance == 0;
        },
        EraseOutcome::Deficit(c) => {
            owns deficit: ctx_at(0, root);
            fact deficit.model == c;
            fact rebalance != 0;
            fact c != Context::Top;
            fact ctx_node_is(c, rebalance) == 1;
        },
    }
}

function erase_leaf_outcome(color: Color, up: Context) -> EraseOutcome {
    match color {
        Color::Red => EraseOutcome::Balanced(plug(up, RbTree::Empty)),
        Color::Black => match up {
            Context::Top => EraseOutcome::Balanced(RbTree::Empty),
            Context::Left(id, above, pc, sibling, outer) => EraseOutcome::Deficit(up),
            Context::Right(id, above, pc, sibling, outer) => EraseOutcome::Deficit(up),
        },
    }
}

// Deeper successor: the minimum's replacement child and color decide whether
// splicing it out leaves a black deficit.
function erase_deep_outcome(tree: RbTree, up: Context, minimum: RbMinimum) -> EraseOutcome {
    match minimum {
        RbMinimum::Absent => EraseOutcome::Balanced(plug(up, erase_child_deep_model(tree))),
        RbMinimum::Found(successor, color, child) => match child {
            RbTree::Empty => match color {
                Color::Red => EraseOutcome::Balanced(plug(up, erase_child_deep_model(tree))),
                Color::Black => EraseOutcome::Deficit(erase_deep_context(tree, up)),
            },
            RbTree::Node(id, parent, child_color, left, right) =>
                EraseOutcome::Balanced(plug(up, erase_child_deep_model(tree))),
        },
    }
}

function erase_deep_splice(tree: RbTree, minimum: RbMinimum) -> RbTree {
    match minimum {
        RbMinimum::Absent => erase_child_deep_model(tree),
        RbMinimum::Found(successor, color, child) => match child {
            RbTree::Empty => match color {
                Color::Red => erase_child_deep_model(tree),
                Color::Black => erase_deep_model(tree),
            },
            RbTree::Node(id, parent, child_color, left, right) => erase_child_deep_model(tree),
        },
    }
}

theorem erase_unlink_red_if_not_black(c: Color) {
    requires not(c == Color::Black);
    ensures c == Color::Red by {
        let ih = induct(c);
        match c {
            Color::Red => { close(); }
            Color::Black => {
                have Color::Black == Color::Black by close();
                contradiction(Color::Black == Color::Black);
            }
        }
    }
}

// A deeper minimum with a nonempty child, or a red leaf minimum, leaves the
// tree balanced.
theorem erase_deep_no_fixup(tree: RbTree, up: Context, successor: struct rb_node*,
    color: Color, child: RbTree) {
    requires not(child == RbTree::Empty) or color == Color::Red;
    ensures erase_deep_outcome(tree, up, RbMinimum::Found(successor, color, child))
        == EraseOutcome::Balanced(plug(up, erase_child_deep_model(tree))) by {
        let ih = induct(child);
        match child {
            RbTree::Empty => {
                cases {
                    not(RbTree::Empty == RbTree::Empty) => {
                        have RbTree::Empty == RbTree::Empty by close();
                        contradiction(RbTree::Empty == RbTree::Empty);
                    }
                    color == Color::Red => {
                        rewrite(color, Color::Red);
                        unfold(erase_deep_outcome(tree, up, RbMinimum::Found(successor, Color::Red, RbTree::Empty)));
                        close();
                    }
                }
            }
            RbTree::Node(id, parent, child_color, left, right) => {
                unfold(erase_deep_outcome(tree, up, RbMinimum::Found(successor, color, RbTree::Node(id, parent, child_color, left, right))));
                close();
            }
        }
    }
    ensures erase_deep_splice(tree, RbMinimum::Found(successor, color, child)) == erase_child_deep_model(tree) by {
        let ih = induct(child);
        match child {
            RbTree::Empty => {
                cases {
                    not(RbTree::Empty == RbTree::Empty) => {
                        have RbTree::Empty == RbTree::Empty by close();
                        contradiction(RbTree::Empty == RbTree::Empty);
                    }
                    color == Color::Red => {
                        rewrite(color, Color::Red);
                        unfold(erase_deep_splice(tree, RbMinimum::Found(successor, Color::Red, RbTree::Empty)));
                        close();
                    }
                }
            }
            RbTree::Node(id, parent, child_color, left, right) => {
                unfold(erase_deep_splice(tree, RbMinimum::Found(successor, color, RbTree::Node(id, parent, child_color, left, right))));
                close();
            }
        }
    }
}

// The C decision sequence: no left child, no right child, immediate
// successor, or deeper successor; then whether the spliced-out node leaves a
// black deficit.
function erase_outcome(tree: RbTree, up: Context) -> EraseOutcome {
    match tree {
        RbTree::Empty => EraseOutcome::Balanced(plug(up, RbTree::Empty)),
        RbTree::Node(node, parent, color, left, right) => match left {
            RbTree::Empty => match right {
                RbTree::Empty => erase_leaf_outcome(color, up),
                RbTree::Node(rid, rp, rc, rl, rr) =>
                    EraseOutcome::Balanced(plug(up, rb_erase_one_child_model(tree))),
            },
            RbTree::Node(lid, lp, lc, ll, lr) => match right {
                RbTree::Empty => EraseOutcome::Balanced(plug(up, rb_erase_one_child_model(tree))),
                RbTree::Node(rid, rp, rc, rl, rr) => match rl {
                    RbTree::Empty => match rr {
                        RbTree::Empty => match rc {
                            Color::Red => EraseOutcome::Balanced(plug(up, rb_erase_immediate_leaf_model(tree))),
                            Color::Black => EraseOutcome::Deficit(rb_erase_immediate_black_context(tree, up)),
                        },
                        RbTree::Node(cid, cp, cc, cl, cr) =>
                            EraseOutcome::Balanced(plug(up, rb_erase_immediate_child_model(tree))),
                    },
                    RbTree::Node(mid, mp, mc, ml, mr) => erase_deep_outcome(tree, up, rb_minimum(right)),
                },
            },
        },
    }
}

// The erased node's replacement subtree in its unchanged outer context.
function erase_splice(tree: RbTree) -> RbTree {
    match tree {
        RbTree::Empty => RbTree::Empty,
        RbTree::Node(node, parent, color, left, right) => match left {
            RbTree::Empty => match right {
                RbTree::Empty => RbTree::Empty,
                RbTree::Node(rid, rp, rc, rl, rr) => rb_erase_one_child_model(tree),
            },
            RbTree::Node(lid, lp, lc, ll, lr) => match right {
                RbTree::Empty => rb_erase_one_child_model(tree),
                RbTree::Node(rid, rp, rc, rl, rr) => match rl {
                    RbTree::Empty => match rr {
                        RbTree::Empty => rb_erase_immediate_leaf_model(tree),
                        RbTree::Node(cid, cp, cc, cl, cr) => rb_erase_immediate_child_model(tree),
                    },
                    RbTree::Node(mid, mp, mc, ml, mr) => erase_deep_splice(tree, rb_minimum(right)),
                },
            },
        },
    }
}

// Below a two-child node whose right child has a left child, the outcome is
// decided by the right subtree's minimum.
theorem erase_outcome_deep(node: struct rb_node*, parent: struct rb_node*, color: Color,
    ln: struct rb_node*, lp: struct rb_node*, lc: Color, ll: RbTree, lr: RbTree,
    rn: struct rb_node*, rp: struct rb_node*, rc: Color,
    mn: struct rb_node*, mp: struct rb_node*, mc: Color, ml: RbTree, mr: RbTree,
    rr: RbTree, up: Context) {
    ensures erase_outcome(RbTree::Node(node, parent, color, RbTree::Node(ln, lp, lc, ll, lr), RbTree::Node(rn, rp, rc, RbTree::Node(mn, mp, mc, ml, mr), rr)), up) == erase_deep_outcome(RbTree::Node(node, parent, color, RbTree::Node(ln, lp, lc, ll, lr), RbTree::Node(rn, rp, rc, RbTree::Node(mn, mp, mc, ml, mr), rr)), up, rb_minimum(RbTree::Node(rn, rp, rc, RbTree::Node(mn, mp, mc, ml, mr), rr))) by {
        unfold(erase_outcome(RbTree::Node(node, parent, color, RbTree::Node(ln, lp, lc, ll, lr), RbTree::Node(rn, rp, rc, RbTree::Node(mn, mp, mc, ml, mr), rr)), up)); close();
    }
    ensures erase_splice(RbTree::Node(node, parent, color, RbTree::Node(ln, lp, lc, ll, lr), RbTree::Node(rn, rp, rc, RbTree::Node(mn, mp, mc, ml, mr), rr))) == erase_deep_splice(RbTree::Node(node, parent, color, RbTree::Node(ln, lp, lc, ll, lr), RbTree::Node(rn, rp, rc, RbTree::Node(mn, mp, mc, ml, mr), rr)), rb_minimum(RbTree::Node(rn, rp, rc, RbTree::Node(mn, mp, mc, ml, mr), rr))) by {
        unfold(erase_splice(RbTree::Node(node, parent, color, RbTree::Node(ln, lp, lc, ll, lr), RbTree::Node(rn, rp, rc, RbTree::Node(mn, mp, mc, ml, mr), rr)))); close();
    }
}

// The whole tree the outcome describes; a deficit context holds an empty hole.
function erase_out_tree(outcome: EraseOutcome) -> RbTree {
    match outcome {
        EraseOutcome::Balanced(t) => t,
        EraseOutcome::Deficit(c) => plug(c, RbTree::Empty),
    }
}

// A balanced outcome is red-black; a deficit context lacks one black level.
function erase_out_rb(outcome: EraseOutcome) -> int32 {
    match outcome {
        EraseOutcome::Balanced(t) => is_rb_root(t),
        EraseOutcome::Deficit(c) => ctx_rb(c, Nat::Succ(Nat::Zero), Color::Black),
    }
}

struct rb_node* __rb_erase_augmented(struct rb_node* node, struct rb_root* root,
                                    const struct rb_augment_callbacks* augment) {
    consumes tree: rb_at(node);
    consumes up: ctx_at(node, root);
    requires tree.model != RbTree::Empty;
    requires is_rb(tree.model) == 1;
    requires ctx_rb(up.model, black_height(tree.model), rb_color(tree.model)) == 1;
    requires ctx_consistent(up.model, tree.model, 0) == 1;
    views erase_callbacks(augment);
    produces node->__rb_parent_color;
    produces node->rb_left;
    produces node->rb_right;
    produces out: erase_out(root, result);
    ensures out.model == erase_outcome(old(tree.model), old(up.model));
    ensures erase_out_rb(out.model) == 1;
    ensures rb_tree_parent_consistent(erase_out_tree(out.model)) == 1;
    ensures erase_out_tree(out.model) == plug(old(up.model), erase_splice(old(tree.model)));
    ensures rb_inorder(erase_splice(old(tree.model)))
        == list::append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model))));
} by {
    // The deeper-successor exits come first: their proofs name the tree's
    // shape themselves.
    if rb_left(tree.model) != RbTree::Empty and rb_right(tree.model) != RbTree::Empty
        and rb_left(rb_right(tree.model)) != RbTree::Empty {
        // Deeper successor: descend to the minimum of the right subtree, splice it
        // out, and transplant it into the erased node's place. A black leaf minimum
        // leaves a deficit at its old parent; otherwise the tree stays balanced.
        if erase_minimum_child(rb_minimum(rb_right(tree.model))) == RbTree::Empty
            and erase_minimum_color(rb_minimum(rb_right(tree.model))) == Color::Black {
            match tree.model {
                RbTree::Empty => { contradiction(tree.model == RbTree::Empty); },
                RbTree::Node(identity, parent_model, color, left_model, right_model) => {
                    have rb_left(tree.model) == left_model by {
                        rewrite(tree.model, RbTree::Node(identity, parent_model, color, left_model, right_model));
                        unfold(rb_left(RbTree::Node(identity, parent_model, color, left_model, right_model))); normalize();
                    }
                    have rb_right(tree.model) == right_model by {
                        rewrite(tree.model, RbTree::Node(identity, parent_model, color, left_model, right_model));
                        unfold(rb_right(RbTree::Node(identity, parent_model, color, left_model, right_model))); normalize();
                    }
                    have left_model != RbTree::Empty by { rewrite(left_model, rb_left(tree.model)); close(); }
                    have right_model != RbTree::Empty by { rewrite(right_model, rb_right(tree.model)); close(); }
                    have erase_minimum_child(rb_minimum(right_model)) == RbTree::Empty by {
                        rewrite(right_model, rb_right(tree.model)); close();
                    }
                    have rb_left(right_model) != RbTree::Empty;
                    apply(erase_context_parent(up.model, identity, parent_model, color, left_model, right_model));
                    apply(ctx_consistent_node_children(up.model, identity, parent_model, color, left_model, right_model, 0));
                    have is_rb(RbTree::Node(identity, parent_model, color, left_model, right_model)) == 1 by {
                        rewrite(RbTree::Node(identity, parent_model, color, left_model, right_model), tree.model); close();
                    }
                    have ctx_rb(up.model, black_height(RbTree::Node(identity, parent_model, color, left_model, right_model)), rb_color(RbTree::Node(identity, parent_model, color, left_model, right_model))) == 1 by {
                        rewrite(RbTree::Node(identity, parent_model, color, left_model, right_model), tree.model); close();
                    }
                    have rb_left(old(tree.model)) == left_model;
                    have rb_right(old(tree.model)) == right_model;
                    let { left: l, right: r } = unfold(tree);
                    mark erased_parent_initial;
                    let old_left = fold(erase_saved_left(node), { child: node->rb_left });
                    match left_model {
                        RbTree::Empty => { contradiction(left_model == RbTree::Empty); },
                        RbTree::Node(lid, lp, lc, ll, lr) => {
                            let { left: ll_tree, right: lr_tree } = unfold(l);
                            let left_color = fold(erase_saved_color(lid), { color: lc });
                            mark before_left_splice;
                            let left_children = fold(erase_saved_children(lid), {
                                left: lid->rb_left, right: lid->rb_right
                            });
                            match right_model {
                                RbTree::Empty => { contradiction(right_model == RbTree::Empty); },
                                RbTree::Node(rid, rp, rc, rl, rr) => {
                                    have rl != RbTree::Empty by {
                                        unfold(rb_left(RbTree::Node(rid, rp, rc, rl, rr)));
                                        rewrite(rl, rb_left(RbTree::Node(rid, rp, rc, rl, rr)));
                                        rewrite(RbTree::Node(rid, rp, rc, rl, rr), right_model); close();
                                    }
                                    apply(rb_parent_consistent_node_left(rid, rp, rc, rl, rr, identity));
                                    let { left: t, right: right_sibling } = unfold(r);
                                    match rl {
                                        RbTree::Empty => { contradiction(rl == RbTree::Empty); },
                                        RbTree::Node(iid, ip, ic, il, ir) => {
                                            let { left: init_l, right: init_r } = unfold(t);
                                            let t = fold(rb_at(iid), { model: RbTree::Node(iid, ip, ic, il, ir), left: init_l, right: init_r });
                                            step(); step(); step(); step(); step(); step(); step(); step(); step(); step(); step(); step(); step(); step();
                                            let c = fold(erase_spine_at(tmp, child), { model: EraseSpine::Top });
                                            have plug(erase_context(c.model), t.model) == rl by {
                                                rewrite(c.model, EraseSpine::Top);
                                                unfold(erase_context(EraseSpine::Top));
                                                unfold(plug(Context::Top, t.model)); close();
                                            }
                                            have successor == erase_spine_parent(c.model, child) by {
                                                rewrite(c.model, EraseSpine::Top);
                                                unfold(erase_spine_parent(EraseSpine::Top, child)); close();
                                            }
                                            loop {
                                                owns c: erase_spine_at(tmp, child);
                                                owns t: rb_at(tmp);
                                                decreases t;
                                                invariant tmp != 0;
                                                invariant successor == erase_spine_parent(c.model, child);
                                                invariant plug(erase_context(c.model), t.model) == rl;
                                                initialize by close();
                                                maintain by {
                                                    match t.model {
                                                        RbTree::Empty => { unfold(t); have tmp != 0 by { close(); } contradiction(tmp == 0); },
                                                        RbTree::Node(tid, tp, tc, tl, tr) => {
                                                            have plug(erase_context(EraseSpine::Left(tid, tp, tc, tr, c.model)), tl) == rl by {
                                                                unfold(erase_context(EraseSpine::Left(tid, tp, tc, tr, c.model)));
                                                                unfold(plug(Context::Left(tid, tp, tc, tr, erase_context(c.model)), tl));
                                                                rewrite(RbTree::Node(tid, tp, tc, tl, tr), t.model); close();
                                                            }
                                                            mark before_spine_unfold;
                                                            let { left: next, right: sibling } = unfold(t);
                                                            have tmp->rb_right == at(before_spine_unfold, tmp->rb_right) by close();
                                                            have tmp == tid;
                                                            have tid != 0;
                                                            have erase_spine_parent(EraseSpine::Left(tid, tp, tc, tr, c.model), child) == tid;
                                                            let frame = fold(erase_spine_at(tmp->rb_left, child),
                                                                { model: EraseSpine::Left(tmp, tp, tc, tr, c.model), up: c, sibling: sibling });
                                                            step(); step(); step();
                                                            have successor == erase_spine_parent(frame.model, child);
                                                            if tmp == 0 {
                                                            } else {
                                                            }
                                                        },
                                                    }
                                                }
                                            }
                                            have node->rb_left == lid;
                                            have tmp == 0;
                                            match t.model {
                                                RbTree::Node(a, b, col, lt, rt) => {
                                                    have t.model == RbTree::Empty;
                                                    have t.model != RbTree::Empty by { rewrite(t.model, RbTree::Node(a, b, col, lt, rt)); normalize(); }
                                                    contradiction(t.model == RbTree::Empty);
                                                },
                                                RbTree::Empty => {
                                                    have c.model != EraseSpine::Top;
                                                    match c.model {
                                                        EraseSpine::Top => { contradiction(c.model == EraseSpine::Top); },
                                                        EraseSpine::Left(mid, mp, mc, mr, mu) => {
                                                            apply(erase_spine_minimum(mu, RbTree::Node(mid, mp, mc, RbTree::Empty, mr)));
                                                            have rb_minimum(rl) == RbMinimum::Found(mid, mc, mr) by {
                                                                rewrite(rl, plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr)));
                                                                rewrite(rb_minimum(plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr))), rb_minimum(RbTree::Node(mid, mp, mc, RbTree::Empty, mr)));
                                                                unfold(rb_minimum(RbTree::Node(mid, mp, mc, RbTree::Empty, mr))); normalize();
                                                            }
                                                            apply(rb_minimum_nonempty_left(rid, rp, rc, rl, rr));
                                                            have rb_minimum(right_model) == RbMinimum::Found(mid, mc, mr) by {
                                                                rewrite(right_model, RbTree::Node(rid, rp, rc, rl, rr));
                                                                rewrite(rb_minimum(RbTree::Node(rid, rp, rc, rl, rr)), rb_minimum(rl)); close();
                                                            }
                                                            have erase_minimum_child(rb_minimum(right_model)) == mr by {
                                                                rewrite(rb_minimum(right_model), RbMinimum::Found(mid, mc, mr));
                                                                unfold(erase_minimum_child(RbMinimum::Found(mid, mc, mr))); normalize();
                                                            }
                                                            have erase_minimum_color(rb_minimum(right_model)) == mc by {
                                                                rewrite(rb_minimum(right_model), RbMinimum::Found(mid, mc, mr));
                                                                unfold(erase_minimum_color(RbMinimum::Found(mid, mc, mr))); normalize();
                                                            }
                                                            apply(rb_erase_black_successor_splice(identity, mid, parent_model, color, left_model, right_model, up.model, 0));
                                                            have erase_minimum_identity(rb_minimum(right_model)) == mid by {
                                                                rewrite(rb_minimum(right_model), RbMinimum::Found(mid, mc, mr));
                                                                unfold(erase_minimum_identity(RbMinimum::Found(mid, mc, mr))); normalize();
                                                            }
                                                            apply(erase_spine_focus_parent_consistent(mu, RbTree::Node(mid, mp, mc, RbTree::Empty, mr), rid));
                                                            apply(erase_parent_consistent_parent_is(RbTree::Node(mid, mp, mc, RbTree::Empty, mr), erase_spine_parent(mu, rid)));
                                                            apply(rb_parent_is_node_parent(mid, mp, mc, RbTree::Empty, mr, erase_spine_parent(mu, rid)));
                                                            apply(erase_spine_links_from_tree(mu, RbTree::Node(mid, mp, mc, RbTree::Empty, mr), rid));
                                                            apply(erase_spine_min_parent(mu, RbTree::Node(mid, mp, mc, RbTree::Empty, mr)));
                                                            apply(rb_min_parent_nonempty_left(rid, rp, rc, rl, rr));
                                                            have rb_min_parent(right_model) == mp by {
                                                                rewrite(right_model, RbTree::Node(rid, rp, rc, rl, rr));
                                                                rewrite(rb_min_parent(RbTree::Node(rid, rp, rc, rl, rr)), rb_min_parent(rl));
                                                                rewrite(rl, plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr)));
                                                                rewrite(rb_min_parent(plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr))), rb_min_parent(RbTree::Node(mid, mp, mc, RbTree::Empty, mr)));
                                                                unfold(rb_min_parent(RbTree::Node(mid, mp, mc, RbTree::Empty, mr))); normalize();
                                                            }
                                                            let { sibling: min_right, up: path } = unfold(c);
                                                            have (mid->__rb_parent_color & 1) == color_bit(mc) by close();
                                                            let successor_color = fold(erase_saved_color(mid), { color: mc });
                                                            unfold(t);
                                                            have parent == erase_spine_parent(path.model, child);
                                                            have parent == mp by {
                                                                rewrite(parent, erase_spine_parent(path.model, child));
                                                                rewrite(path.model, mu); rewrite(child, rid);
                                                                rewrite(erase_spine_parent(mu, rid), mp); normalize();
                                                            }
                                                            have path.model == mu;
                                                            mark opened_spine;
                                                            let { frame: link_frame } = open_erase_spine_link(successor, parent, child, { c: path });
                                                            have link_frame.model == at(opened_spine, path.model) by close();
                                                            let saved_color = fold(erase_saved_color(child), { color: rc });
                                                            step(); // Read the successor’s right child.
                                                            mark before_detaching_successor;
                                                            have *((&node->__rb_parent_color) as (int32**)) == at(erased_parent_initial, *((&node->__rb_parent_color) as (int32**))) by close();
                                                            have separate(memory(parent->rb_left), memory(node->__rb_parent_color)) by close();
                                                            step();
                                                            mark after_detaching_successor;
                                                            have separate(region(36).footprint, memory(node->__rb_parent_color)) by {
                                                                normalize() using { separate(memory(parent->rb_left), memory(node->__rb_parent_color)); };
                                                            }
                                                            have *((&node->__rb_parent_color) as (int32**)) == at(before_detaching_successor, *((&node->__rb_parent_color) as (int32**))) by {
                                                                preserve(memory(node->__rb_parent_color), region(36));
                                                            }
                                                            have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == parent_model by close();
                                                            mark before_linking_successor;
                                                            have separate(memory(successor->rb_right), memory(node->__rb_parent_color)) by close();
                                                            step();
                                                            mark after_linking_successor;
                                                            have separate(region(37).footprint, memory(node->__rb_parent_color)) by {
                                                                normalize() using { separate(memory(successor->rb_right), memory(node->__rb_parent_color)); };
                                                            }
                                                            have *((&node->__rb_parent_color) as (int32**)) == at(before_linking_successor, *((&node->__rb_parent_color) as (int32**))) by {
                                                                preserve(memory(node->__rb_parent_color), region(37));
                                                            }
                                                            have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == parent_model by close();
                                                            unfold(saved_color);
                                                            have (child->__rb_parent_color & 1) == color_bit(rc) by close();
                                                            mark before_reparent;
                                                            have separate(memory(child->__rb_parent_color), memory(node->__rb_parent_color)) by close();
                                                            step();
                                                            mark after_child_reparent;
                                                            have contains(memory(child->__rb_parent_color), region(38).footprint) by close();
                                                            apply(click::separation::contains_refl(memory(node->__rb_parent_color)));
                                                            apply(click::separation::separate_restrict(memory(child->__rb_parent_color), memory(node->__rb_parent_color), region(38).footprint, memory(node->__rb_parent_color)));
                                                            have *((&node->__rb_parent_color) as (int32**)) == at(before_reparent, *((&node->__rb_parent_color) as (int32**))) by {
                                                                preserve(memory(node->__rb_parent_color), region(38));
                                                            }
                                                            have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == parent_model by close();
                                                            apply(packed_parent_word(successor, at(before_reparent, child->__rb_parent_color)));
                                                            have child->__rb_parent_color == address(mid) + (child->__rb_parent_color & 1) by {
                                                                rewrite(child->__rb_parent_color, ((at(before_reparent, child->__rb_parent_color) & 1) | address(successor)));
                                                                rewrite(mid, successor);
                                                                close();
                                                            }
                                                            have (child->__rb_parent_color & 1) == (at(before_reparent, child->__rb_parent_color) & 1) by {
                                                                rewrite(child->__rb_parent_color, ((at(before_reparent, child->__rb_parent_color) & 1) | address(successor)));
                                                                close();
                                                            }
                                                            have (child->__rb_parent_color & 1) == color_bit(rc) by {
                                                                rewrite((child->__rb_parent_color & 1), (at(before_reparent, child->__rb_parent_color) & 1));
                                                                close();
                                                            }
                                                            have min_right.model == RbTree::Empty by { rewrite(min_right.model, mr); close(); }
                                                            unfold(min_right);
                                                            have color_bit(mc) == 1 by { rewrite(mc, Color::Black); unfold(color_bit(Color::Black)); normalize(); }
                                                            with(erase_callbacks(augment)) {
                                                                mark before_copy;
                                                                step();
                                                                have separate(region(39).footprint, memory(node->__rb_parent_color)) by {
                                                                    normalize() using { };
                                                                }
                                                                have *((&node->__rb_parent_color) as (int32**)) == at(before_copy, *((&node->__rb_parent_color) as (int32**))) by {
                                                                    preserve(memory(node->__rb_parent_color), region(39));
                                                                }
                                                                have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == parent_model by close();
                                                                mark before_propagate;
                                                                step();
                                                                have separate(region(40).footprint, memory(node->__rb_parent_color)) by {
                                                                    normalize() using { };
                                                                }
                                                                have *((&node->__rb_parent_color) as (int32**)) == at(before_propagate, *((&node->__rb_parent_color) as (int32**))) by {
                                                                    preserve(memory(node->__rb_parent_color), region(40));
                                                                }
                                                                have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == parent_model by close();
                                                            }
                                                            have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == parent_model by close();
                                                            unfold(old_left);
                                                            have node->rb_left == lid by close();
                                                            mark before_reading_left_child;
                                                            step();
                                                            have separate(region(41).footprint, memory(node->__rb_parent_color)) by {
                                                                normalize() using { };
                                                            }
                                                            have *((&node->__rb_parent_color) as (int32**)) == at(before_reading_left_child, *((&node->__rb_parent_color) as (int32**))) by {
                                                                preserve(memory(node->__rb_parent_color), region(41));
                                                            }
                                                            have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == parent_model by close();
                                                            mark before_linking_left_child;
                                                            have separate(memory(successor->rb_left), memory(node->__rb_parent_color)) by close();
                                                            step();
                                                            mark after_linking_left_child;
                                                            have separate(region(42).footprint, memory(node->__rb_parent_color)) by {
                                                                normalize() using { separate(memory(successor->rb_left), memory(node->__rb_parent_color)); };
                                                            }
                                                            have *((&node->__rb_parent_color) as (int32**)) == at(before_linking_left_child, *((&node->__rb_parent_color) as (int32**))) by {
                                                                preserve(memory(node->__rb_parent_color), region(42));
                                                            }
                                                            have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == parent_model by close();
                                                            unfold(left_color);
                                                            have (tmp->__rb_parent_color & 1) == color_bit(lc) by close();
                                                            // Rebind tag ownership to the live C argument.
                                                            let live_left_tag = fold(erase_saved_color(tmp), { color: lc });
                                                            unfold(live_left_tag);
                                                            have separate(memory(tmp->__rb_parent_color), memory(*augment)) by close();
                                                            mark before_left_reparent;
                                                            step();
                                                            mark after_left_reparent;
                                                            have separate(at(before_left_reparent, memory(tmp->__rb_parent_color)), memory(node->__rb_parent_color)) by close();
                                                            have separate(region(43).footprint, memory(node->__rb_parent_color)) by {
                                                                normalize() using { separate(at(before_left_reparent, memory(tmp->__rb_parent_color)), memory(node->__rb_parent_color)); };
                                                            }
                                                            have *((&node->__rb_parent_color) as (int32**)) == at(before_left_reparent, *((&node->__rb_parent_color) as (int32**))) by {
                                                                preserve(memory(node->__rb_parent_color), region(43));
                                                            }
                                                            have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == parent_model by close();
                                                            have contains(at(before_left_reparent, memory(tmp->__rb_parent_color)), region(43).footprint) by close();
                                                            have separate(at(before_left_reparent, memory(tmp->__rb_parent_color)), memory(successor->rb_left)) by close();
                                                            apply(click::separation::contains_refl(memory(successor->rb_left)));
                                                            apply(click::separation::separate_restrict(at(before_left_reparent, memory(tmp->__rb_parent_color)), memory(successor->rb_left), region(43).footprint, memory(successor->rb_left)));
                                                            have at(after_linking_left_child, successor->rb_left) == lid by close();
                                                            have at(before_left_reparent, successor->rb_left) == at(after_linking_left_child, successor->rb_left) by close();
                                                            have successor->rb_left == at(before_left_reparent, successor->rb_left) by {
                                                                preserve(memory(successor->rb_left), region(43));
                                                            }
                                                            have successor->rb_left == lid by close();
                                                            have separate(memory(successor->rb_left), memory(child->__rb_parent_color)) by close();
                                                            have separate(memory(successor->rb_left), memory(parent->rb_left)) by close();
                                                            have at(before_detaching_successor, child->rb_right) == at(erased_parent_initial, node->rb_right->rb_right) by close();
                                                            have separate(memory(parent->rb_left), memory(child->rb_right)) by close();
                                                            have separate(region(36).footprint, memory(child->rb_right)) by {
                                                                normalize() using { separate(memory(parent->rb_left), memory(child->rb_right)); };
                                                            }
                                                            have at(after_detaching_successor, child->rb_right) == at(before_detaching_successor, child->rb_right) by {
                                                                preserve(memory(child->rb_right), region(36));
                                                            }
                                                            have at(after_detaching_successor, child->rb_right) == at(erased_parent_initial, node->rb_right->rb_right) by close();
                                                            have at(before_linking_successor, child->rb_right) == at(after_detaching_successor, child->rb_right) by close();
                                                            have separate(memory(successor->rb_right), memory(child->rb_right)) by close();
                                                            have separate(region(37).footprint, memory(child->rb_right)) by {
                                                                normalize() using { separate(memory(successor->rb_right), memory(child->rb_right)); };
                                                            }
                                                            have at(after_linking_successor, child->rb_right) == at(before_linking_successor, child->rb_right) by {
                                                                preserve(memory(child->rb_right), region(37));
                                                            }
                                                            have at(after_linking_successor, child->rb_right) == at(erased_parent_initial, node->rb_right->rb_right) by close();
                                                            have at(before_reparent, child->rb_right) == at(after_linking_successor, child->rb_right) by close();
                                                            have separate(memory(child->__rb_parent_color), memory(child->rb_right)) by { normalize() using { }; }
                                                            have separate(region(38).footprint, memory(child->rb_right)) by {
                                                                normalize() using { separate(memory(child->__rb_parent_color), memory(child->rb_right)); };
                                                            }
                                                            have at(after_child_reparent, child->rb_right) == at(before_reparent, child->rb_right) by {
                                                                preserve(memory(child->rb_right), region(38));
                                                            }
                                                            have at(after_child_reparent, child->rb_right) == at(erased_parent_initial, node->rb_right->rb_right) by close();
                                                            have at(before_copy, child->rb_right) == at(after_child_reparent, child->rb_right) by close();
                                                            have separate(region(39).footprint, memory(child->rb_right)) by {
                                                                normalize() using { };
                                                            }
                                                            have at(before_propagate, child->rb_right) == at(before_copy, child->rb_right) by {
                                                                preserve(memory(child->rb_right), region(39));
                                                            }
                                                            have at(before_propagate, child->rb_right) == at(erased_parent_initial, node->rb_right->rb_right) by close();
                                                            have separate(region(40).footprint, memory(child->rb_right)) by {
                                                                normalize() using { };
                                                            }
                                                            have at(before_reading_left_child, child->rb_right) == at(before_propagate, child->rb_right) by {
                                                                preserve(memory(child->rb_right), region(40));
                                                            }
                                                            have at(before_reading_left_child, child->rb_right) == at(erased_parent_initial, node->rb_right->rb_right) by close();
                                                            have separate(region(41).footprint, memory(child->rb_right)) by {
                                                                normalize() using { };
                                                            }
                                                            have at(before_linking_left_child, child->rb_right) == at(before_reading_left_child, child->rb_right) by {
                                                                preserve(memory(child->rb_right), region(41));
                                                            }
                                                            have at(before_linking_left_child, child->rb_right) == at(erased_parent_initial, node->rb_right->rb_right) by close();
                                                            have separate(memory(successor->rb_left), memory(child->rb_right)) by close();
                                                            have separate(region(42).footprint, memory(child->rb_right)) by {
                                                                normalize() using { separate(memory(successor->rb_left), memory(child->rb_right)); };
                                                            }
                                                            have at(after_linking_left_child, child->rb_right) == at(before_linking_left_child, child->rb_right) by {
                                                                preserve(memory(child->rb_right), region(42));
                                                            }
                                                            have at(after_linking_left_child, child->rb_right) == at(erased_parent_initial, node->rb_right->rb_right) by close();
                                                            have at(before_left_reparent, child->rb_right) == at(after_linking_left_child, child->rb_right) by close();
                                                            have separate(at(before_left_reparent, memory(tmp->__rb_parent_color)), memory(child->rb_right)) by close();
                                                            apply(click::separation::contains_refl(memory(child->rb_right)));
                                                            apply(click::separation::separate_restrict(at(before_left_reparent, memory(tmp->__rb_parent_color)), memory(child->rb_right), region(43).footprint, memory(child->rb_right)));
                                                            have at(after_left_reparent, child->rb_right) == at(before_left_reparent, child->rb_right) by {
                                                                preserve(memory(child->rb_right), region(43));
                                                            }
                                                            have at(after_left_reparent, child->rb_right) == at(erased_parent_initial, node->rb_right->rb_right) by close();
                                                            have aligned(successor, 8) by close();
                                                            have aligned(successor, 8) implies at(after_child_reparent, ((child->__rb_parent_color & ~3) as (struct rb_node *))) == successor by close();
                                                            have at(after_child_reparent, ((child->__rb_parent_color & ~3) as (struct rb_node *))) == successor by {
                                                                close() using {
                                                                    aligned(successor, 8);
                                                                    aligned(successor, 8) implies at(after_child_reparent, ((child->__rb_parent_color & ~3) as (struct rb_node *))) == successor;
                                                                };
                                                            }
                                                            have at(before_copy, *((&child->__rb_parent_color) as (int32**))) == at(after_child_reparent, *((&child->__rb_parent_color) as (int32**))) by close();
                                                            have separate(region(39).footprint, memory(child->__rb_parent_color)) by {
                                                                normalize() using { };
                                                            }
                                                            have at(before_propagate, *((&child->__rb_parent_color) as (int32**))) == at(before_copy, *((&child->__rb_parent_color) as (int32**))) by {
                                                                preserve(memory(child->__rb_parent_color), region(39));
                                                            }
                                                            have at(before_propagate, *((&child->__rb_parent_color) as (int32**))) == at(after_child_reparent, *((&child->__rb_parent_color) as (int32**))) by close();
                                                            have at(before_propagate, ((child->__rb_parent_color & ~3) as (struct rb_node *))) == successor by close();
                                                            have separate(region(40).footprint, memory(child->__rb_parent_color)) by {
                                                                normalize() using { };
                                                            }
                                                            have at(before_reading_left_child, *((&child->__rb_parent_color) as (int32**))) == at(before_propagate, *((&child->__rb_parent_color) as (int32**))) by {
                                                                preserve(memory(child->__rb_parent_color), region(40));
                                                            }
                                                            have at(before_reading_left_child, *((&child->__rb_parent_color) as (int32**))) == at(after_child_reparent, *((&child->__rb_parent_color) as (int32**))) by close();
                                                            have at(before_reading_left_child, ((child->__rb_parent_color & ~3) as (struct rb_node *))) == successor by close();
                                                            have separate(region(41).footprint, memory(child->__rb_parent_color)) by {
                                                                normalize() using { };
                                                            }
                                                            have at(before_linking_left_child, *((&child->__rb_parent_color) as (int32**))) == at(before_reading_left_child, *((&child->__rb_parent_color) as (int32**))) by {
                                                                preserve(memory(child->__rb_parent_color), region(41));
                                                            }
                                                            have at(before_linking_left_child, *((&child->__rb_parent_color) as (int32**))) == at(after_child_reparent, *((&child->__rb_parent_color) as (int32**))) by close();
                                                            have at(before_linking_left_child, ((child->__rb_parent_color & ~3) as (struct rb_node *))) == successor by close();
                                                            have separate(memory(successor->rb_left), memory(child->__rb_parent_color)) by close();
                                                            have separate(region(42).footprint, memory(child->__rb_parent_color)) by {
                                                                normalize() using { separate(memory(successor->rb_left), memory(child->__rb_parent_color)); };
                                                            }
                                                            have at(after_linking_left_child, *((&child->__rb_parent_color) as (int32**))) == at(before_linking_left_child, *((&child->__rb_parent_color) as (int32**))) by {
                                                                preserve(memory(child->__rb_parent_color), region(42));
                                                            }
                                                            have at(after_linking_left_child, *((&child->__rb_parent_color) as (int32**))) == at(after_child_reparent, *((&child->__rb_parent_color) as (int32**))) by close();
                                                            have at(after_linking_left_child, child->__rb_parent_color) == at(before_linking_left_child, child->__rb_parent_color) by {
                                                                preserve(memory(child->__rb_parent_color), region(42));
                                                            }
                                                            have at(after_linking_left_child, ((child->__rb_parent_color & ~3) as (struct rb_node *))) == successor by {
                                                                rewrite(at(after_linking_left_child, child->__rb_parent_color), at(before_linking_left_child, child->__rb_parent_color));
                                                                close();
                                                            }
                                                            have at(before_left_reparent, *((&child->__rb_parent_color) as (int32**))) == at(after_linking_left_child, *((&child->__rb_parent_color) as (int32**))) by close();
                                                            have separate(at(before_left_reparent, memory(tmp->__rb_parent_color)), memory(child->__rb_parent_color)) by close();
                                                            apply(click::separation::contains_refl(memory(child->__rb_parent_color)));
                                                            apply(click::separation::separate_restrict(at(before_left_reparent, memory(tmp->__rb_parent_color)), memory(child->__rb_parent_color), region(43).footprint, memory(child->__rb_parent_color)));
                                                            have *((&child->__rb_parent_color) as (int32**)) == at(before_left_reparent, *((&child->__rb_parent_color) as (int32**))) by {
                                                                preserve(memory(child->__rb_parent_color), region(43));
                                                            }
                                                            have *((&child->__rb_parent_color) as (int32**)) == at(after_child_reparent, *((&child->__rb_parent_color) as (int32**))) by close();
                                                            have at(before_left_reparent, child->__rb_parent_color) == at(after_linking_left_child, child->__rb_parent_color) by close();
                                                            have at(before_left_reparent, ((child->__rb_parent_color & ~3) as (struct rb_node *))) == successor by close();
                                                            have child->__rb_parent_color == at(before_left_reparent, child->__rb_parent_color) by {
                                                                preserve(memory(child->__rb_parent_color), region(43));
                                                            }
                                                            have ((child->__rb_parent_color & ~3) as (struct rb_node *)) == successor by {
                                                                rewrite(child->__rb_parent_color, at(before_left_reparent, child->__rb_parent_color));
                                                                close();
                                                            }
                                                            let transplanted_left = fold(erase_saved_left(successor), { child: lid });
                                                            have at(after_linking_successor, successor->rb_right) == child by close();
                                                            have at(before_reparent, successor->rb_right) == at(after_linking_successor, successor->rb_right) by close();
                                                            have separate(memory(child->__rb_parent_color), memory(successor->rb_right)) by close();
                                                            have separate(region(38).footprint, memory(successor->rb_right)) by {
                                                                normalize() using { separate(memory(child->__rb_parent_color), memory(successor->rb_right)); };
                                                            }
                                                            have at(after_child_reparent, successor->rb_right) == at(before_reparent, successor->rb_right) by {
                                                                preserve(memory(successor->rb_right), region(38));
                                                            }
                                                            have at(after_child_reparent, successor->rb_right) == child by close();
                                                            have at(before_copy, successor->rb_right) == at(after_child_reparent, successor->rb_right) by close();
                                                            have separate(region(39).footprint, memory(successor->rb_right)) by {
                                                                normalize() using { };
                                                            }
                                                            have at(before_propagate, successor->rb_right) == at(before_copy, successor->rb_right) by {
                                                                preserve(memory(successor->rb_right), region(39));
                                                            }
                                                            have at(before_propagate, successor->rb_right) == child by close();
                                                            have separate(region(40).footprint, memory(successor->rb_right)) by {
                                                                normalize() using { };
                                                            }
                                                            have at(before_reading_left_child, successor->rb_right) == at(before_propagate, successor->rb_right) by {
                                                                preserve(memory(successor->rb_right), region(40));
                                                            }
                                                            have at(before_reading_left_child, successor->rb_right) == child by close();
                                                            have separate(region(41).footprint, memory(successor->rb_right)) by {
                                                                normalize() using { };
                                                            }
                                                            have at(before_linking_left_child, successor->rb_right) == at(before_reading_left_child, successor->rb_right) by {
                                                                preserve(memory(successor->rb_right), region(41));
                                                            }
                                                            have at(before_linking_left_child, successor->rb_right) == child by close();
                                                            have separate(memory(successor->rb_left), memory(successor->rb_right)) by { normalize() using { }; }
                                                            have separate(region(42).footprint, memory(successor->rb_right)) by {
                                                                normalize() using { separate(memory(successor->rb_left), memory(successor->rb_right)); };
                                                            }
                                                            have at(after_linking_left_child, successor->rb_right) == at(before_linking_left_child, successor->rb_right) by {
                                                                preserve(memory(successor->rb_right), region(42));
                                                            }
                                                            have at(after_linking_left_child, successor->rb_right) == child by close();
                                                            have at(before_left_reparent, successor->rb_right) == at(after_linking_left_child, successor->rb_right) by close();
                                                            have separate(at(before_left_reparent, memory(tmp->__rb_parent_color)), memory(successor->rb_right)) by close();
                                                            apply(click::separation::contains_refl(memory(successor->rb_right)));
                                                            apply(click::separation::separate_restrict(at(before_left_reparent, memory(tmp->__rb_parent_color)), memory(successor->rb_right), region(43).footprint, memory(successor->rb_right)));
                                                            have successor->rb_right == at(before_left_reparent, successor->rb_right) by {
                                                                preserve(memory(successor->rb_right), region(43));
                                                            }
                                                            have successor->rb_right == child by close();
                                                            have separate(memory(successor->rb_right), memory(parent->rb_left)) by close();
                                                            let transplanted_right = fold(erase_saved_right(successor), { child: child });
                                                            have separate(memory(child->__rb_parent_color), at(before_left_reparent, memory(tmp->__rb_parent_color))) by close();
                                                            have separate(memory(child->__rb_parent_color), memory(parent->rb_left)) by close();
                                                            have separate(memory(child->rb_right), memory(child->__rb_parent_color)) by close();
                                                            have ((child->__rb_parent_color & ~3) as (struct rb_node *)) == mid by {
                                                                rewrite(mid, successor); close();
                                                            }
                                                            let retained_anchor_tag = fold(erase_saved_parent(child, mid), {
                                                                word: child->__rb_parent_color, color: rc
                                                            });
                                                            have aligned(successor, 8) by close();
                                                            have ((tmp->__rb_parent_color & ~3) as (struct rb_node *)) == successor by {
                                                                close() using {
                                                                    aligned(successor, 8);
                                                                    aligned(successor, 8) implies ((tmp->__rb_parent_color & ~3) as (struct rb_node *)) == successor;
                                                                };
                                                            }
                                                            apply(packed_parent_word(successor, at(before_left_reparent, tmp->__rb_parent_color)));
                                                            have tmp->__rb_parent_color == address(successor) + (tmp->__rb_parent_color & 1) by {
                                                                rewrite(tmp->__rb_parent_color, ((at(before_left_reparent, tmp->__rb_parent_color) & 1) | address(successor)));
                                                                close();
                                                            }
                                                            have (tmp->__rb_parent_color & 1) == color_bit(lc) by {
                                                                rewrite(tmp->__rb_parent_color, ((at(before_left_reparent, tmp->__rb_parent_color) & 1) | address(successor)));
                                                                rewrite(((at(before_left_reparent, tmp->__rb_parent_color) & 1) | address(successor)) & 1,
                                                                    at(before_left_reparent, tmp->__rb_parent_color) & 1);
                                                                close();
                                                            }
                                                            let moved_parent = fold(erase_saved_parent(tmp, successor), {
                                                                word: tmp->__rb_parent_color, color: lc
                                                            });
                                                            unfold(left_children);
                                                            unfold(moved_parent);
                                                            have tmp->rb_left == at(before_left_splice, lid->rb_left) by close();
                                                            have tmp->rb_right == at(before_left_splice, lid->rb_right) by close();
                                                            let moved_left = fold(rb_at(tmp), {
                                                                model: RbTree::Node(lid, successor, lc, ll, lr),
                                                                left: ll_tree, right: lr_tree
                                                            });
                                                            have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == parent_model by close();
                                                            mark before_reading_packed_parent;
                                                            step();
                                                            have separate(region(44).footprint, memory(node->__rb_parent_color)) by {
                                                                normalize() using { };
                                                            }
                                                            have *((&node->__rb_parent_color) as (int32**)) == at(before_reading_packed_parent, *((&node->__rb_parent_color) as (int32**))) by {
                                                                preserve(memory(node->__rb_parent_color), region(44));
                                                            }
                                                            have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == parent_model by close();
                                                            have ((pc & ~3) as (struct rb_node *)) == parent_model by close();
                                                            step();
                                                            have separate(memory(child->rb_right), memory(lid->__rb_parent_color));
                                                            have separate(memory(child->rb_right), memory(node->__rb_parent_color));
                                                            have separate(memory(child->rb_right), memory(parent->rb_left));
                                                            have separate(memory(child->rb_right), memory(mid->rb_left));
                                                            have separate(memory(child->rb_right), memory(child->__rb_parent_color));
                                                            have moved_left.model == rb_reparent(left_model, mid) by {
                                                                rewrite(left_model, RbTree::Node(lid, lp, lc, ll, lr));
                                                                unfold(rb_reparent(RbTree::Node(lid, lp, lc, ll, lr), mid));
                                                                rewrite(successor, mid); normalize();
                                                            }
                                                            have tmp == parent_model;
                                                            have ctx_node_is(up.model, tmp) == 1 by {
                                                                rewrite(tmp, parent_model); close();
                                                            }

                                                            have successor == mid;
                                                            have aligned(successor, 8);
                                                            have child == rid;

                                                            mark transplant;
                                                            have ctx_node_is(up.model, tmp) == 1;
                                                            let { links: incoming, frame: outer_frame } = detach_erase_links(node, tmp, root, { before: up });
                                                            observe(erase_callbacks(augment));
                                                            mark incoming_link_state;
                                                            let { sibling_ptr: sibling_ptr, root_count: root_count, parent_count: parent_count, tag: parent_tag, above: above } = unfold(incoming);
                                                            have separate(memory(root[0..root_count]), memory(*augment)) by close();
                                                            have separate(memory(tmp[0..parent_count]), memory(*augment)) by close();
                                                            let incoming = fold(erase_change_links(node, tmp, root), {
                                                                model: at(incoming_link_state, incoming.model), sibling_ptr: sibling_ptr,
                                                                root_count: root_count, parent_count: parent_count, tag: parent_tag, above: above
                                                            });
                                                            let { updated: linked } = step(__rb_change_child, { links: incoming });
                                                            have linked.model == outer_frame.model;
                                                            have linked.sibling_ptr == outer_frame.sibling_ptr;
                                                            have linked.tag == outer_frame.tag;
                                                            have linked.above == outer_frame.above;
                                                            let { updated: root_context } = attach_erase_links(successor, tmp, root, { links: linked, frame: outer_frame });
                                                            have child->rb_right == at(transplant, child->rb_right);
                                                            have at(transplant, child->rb_right) == at(after_left_reparent, child->rb_right) by close();
                                                            have child->rb_right == at(erased_parent_initial, node->rb_right->rb_right) by close();
                                                            let retained_child_right = fold(erase_saved_right(child), { child: at(erased_parent_initial, node->rb_right->rb_right) });
                                                            have parent->rb_left == at(transplant, parent->rb_left) by { close(); }
                                                            have child2 == 0 by close();
                                                            have at(after_detaching_successor, parent->rb_left) == child2 by close();
                                                            have at(before_linking_successor, parent->rb_left) == at(after_detaching_successor, parent->rb_left) by close();
                                                            have separate(region(37).footprint, memory(parent->rb_left)) by {
                                                                normalize() using { separate(memory(successor->rb_right), memory(parent->rb_left)); };
                                                            }
                                                            have at(after_linking_successor, parent->rb_left) == at(before_linking_successor, parent->rb_left) by {
                                                                preserve(memory(parent->rb_left), region(37));
                                                            }
                                                            have at(after_linking_successor, parent->rb_left) == child2 by close();
                                                            have at(before_reparent, parent->rb_left) == at(after_linking_successor, parent->rb_left) by close();
                                                            have separate(memory(child->__rb_parent_color), memory(parent->rb_left)) by close();
                                                            have separate(region(38).footprint, memory(parent->rb_left)) by {
                                                                normalize() using { separate(memory(child->__rb_parent_color), memory(parent->rb_left)); };
                                                            }
                                                            have at(after_child_reparent, parent->rb_left) == at(before_reparent, parent->rb_left) by {
                                                                preserve(memory(parent->rb_left), region(38));
                                                            }
                                                            have at(after_child_reparent, parent->rb_left) == child2 by close();
                                                            have at(before_copy, parent->rb_left) == at(after_child_reparent, parent->rb_left) by close();
                                                            have separate(region(39).footprint, memory(parent->rb_left)) by {
                                                                normalize() using { };
                                                            }
                                                            have at(before_propagate, parent->rb_left) == at(before_copy, parent->rb_left) by {
                                                                preserve(memory(parent->rb_left), region(39));
                                                            }
                                                            have at(before_propagate, parent->rb_left) == child2 by close();
                                                            have separate(region(40).footprint, memory(parent->rb_left)) by {
                                                                normalize() using { };
                                                            }
                                                            have at(before_reading_left_child, parent->rb_left) == at(before_propagate, parent->rb_left) by {
                                                                preserve(memory(parent->rb_left), region(40));
                                                            }
                                                            have at(before_reading_left_child, parent->rb_left) == child2 by close();
                                                            have separate(region(41).footprint, memory(parent->rb_left)) by {
                                                                normalize() using { };
                                                            }
                                                            have at(before_linking_left_child, parent->rb_left) == at(before_reading_left_child, parent->rb_left) by {
                                                                preserve(memory(parent->rb_left), region(41));
                                                            }
                                                            have at(before_linking_left_child, parent->rb_left) == child2 by close();
                                                            have at(before_linking_left_child, parent->rb_left) == 0 by close();
                                                            have separate(memory(successor->rb_left), memory(parent->rb_left)) by close();
                                                            have separate(region(42).footprint, memory(parent->rb_left)) by {
                                                                normalize() using { separate(memory(successor->rb_left), memory(parent->rb_left)); };
                                                            }
                                                            have at(after_linking_left_child, parent->rb_left) == at(before_linking_left_child, parent->rb_left) by {
                                                                preserve(memory(parent->rb_left), region(42));
                                                            }
                                                            have parent->rb_left == at(after_linking_left_child, parent->rb_left) by close();
                                                            have parent->rb_left == 0 by close();
                                                            have root_context.model == at(transplant, up.model) by close();
                                                            have root_context.model == old(up.model);
                                                            mark parent_link_changed;
                                                            step();
                                                            unfold(successor_color);
                                                            have (mid->__rb_parent_color & 1) == color_bit(mc) by close();
                                                            have (successor->__rb_parent_color & 1) == 1 by {
                                                                rewrite(successor, mid);
                                                                rewrite((mid->__rb_parent_color & 1), color_bit(mc));
                                                                rewrite(color_bit(mc), 1); normalize();
                                                            }
                                                            step_until(statement(4).statement(5).statement(15).entry);
                                                            mark before_copying_tag;
                                                            have ((pc & ~3) as (struct rb_node *)) == parent_model by close();
                                                            step();
                                                            have successor->__rb_parent_color == at(before_copying_tag, pc) by close();
                                                            have ((successor->__rb_parent_color & ~3) as (struct rb_node *)) == parent_model by close();
                                                            let transplanted_tag = fold(erase_saved_parent(successor, parent_model), {
                                                                word: at(before_copying_tag, pc), color: color
                                                            });
                                                            step_until(statement(5).entry);
                                                            have tmp == mid;
                                                            let hole = fold(rb_at(0), { model: RbTree::Empty });
                                                            have parent->rb_left == 0;
                                                            mark closing_spine;
                                                            let { c: path2 } = close_erase_spine_link(0, parent, child, { frame: link_frame });
                                                            apply(rb_reparent_parent_is(left_model, mid));
                                                            have rb_parent_is(rb_reparent(left_model, mid), mid) == 1 by close();
                                                            unfold(transplanted_left);
                                                            have (at(after_left_reparent, successor))->rb_left == lid by close();
                                                            have mid == at(after_left_reparent, successor) by close();
                                                            unfold(transplanted_right);
                                                            have (at(after_left_reparent, successor))->rb_right == child by close();
                                                            have tmp->rb_left == lid by close();
                                                            have tmp->rb_right == child by close();
                                                            unfold(transplanted_tag);
                                                            have ((tmp->__rb_parent_color & ~3) as (struct rb_node *)) == parent_model by close();
                                                            let above = fold(ctx_at(child, root), {
                                                                model: Context::Right(tmp, parent_model, color, rb_reparent(left_model, mid), old(up.model)),
                                                                sibling: moved_left, up: root_context
                                                            });
                                                            have above.model == Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)) by {
                                                                rewrite(above.model, Context::Right(tmp, parent_model, color, rb_reparent(left_model, mid), old(up.model)));
                                                                rewrite(tmp, mid);
                                                                normalize();
                                                            }
                                                            have ctx_node_is(above.model, mid) == 1 by {
                                                                rewrite(above.model, Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)));
                                                                unfold(ctx_node_is(Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)), mid)); normalize();
                                                            }
                                                            have above.model == ctx_reroot(above.model, mid) by {
                                                                rewrite(above.model, Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)));
                                                                unfold(ctx_reroot(Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)), mid)); normalize();
                                                            }
                                                            unfold(retained_child_right);
                                                            have child->rb_right == at(transplant, child->rb_right) by close();
                                                            have child->rb_right == at(erased_parent_initial, node->rb_right->rb_right) by close();
                                                            unfold(retained_anchor_tag);
                                                            have ((child->__rb_parent_color & ~3) as (struct rb_node *)) == mid by close();
                                                            have right_sibling.model == rr;
                                                            let anchor_frame = fold(erase_anchor_frame(child, root), {
                                                                model: EraseAnchorFrame::At(mid, rc, rr, Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model))),
                                                                right: right_sibling, up: above
                                                            });
                                                            have erase_spine_links(path2.model, child) == 1 by {
                                                                rewrite(path2.model, mu); rewrite(child, rid); close();
                                                            }
                                                            mark grafting;
                                                            let { context: deficit } = graft_erase_spine(0, child, root, { c: path2, base: anchor_frame });
                                                            have deficit.model == ctx_concat(erase_context(at(grafting, path2.model)),
                                                                erase_anchor_context(child, EraseAnchorFrame::At(mid, rc, rr, Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model))))) by { close(); }
                                                            have at(grafting, path2.model) == mu by close();
                                                            have erase_anchor_context(child, EraseAnchorFrame::At(mid, rc, rr,
                                                                Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model))))
                                                                == Context::Left(rid, mid, rc, rr, Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model))) by {
                                                                unfold(erase_anchor_context(child, EraseAnchorFrame::At(mid, rc, rr,
                                                                    Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)))));
                                                                rewrite(child, rid); normalize();
                                                            }
                                                            have deficit.model == ctx_concat(erase_context(mu),
                                                                Context::Left(rid, mid, rc, rr, Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)))) by {
                                                                rewrite(mu, at(grafting, path2.model));
                                                                rewrite(Context::Left(rid, mid, rc, rr, Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model))), erase_anchor_context(child, EraseAnchorFrame::At(mid, rc, rr,
                                                                        Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)))));
                                                                close();
                                                            }
                                                            apply(erase_spine_min_context(mu, RbTree::Node(mid, mp, mc, RbTree::Empty, mr),
                                                                Context::Left(rid, mid, rc, rr, Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)))));
                                                            apply(rb_min_context_nonempty_left(rid, mid, rc, rl, rr,
                                                                Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model))));
                                                            have rb_successor_context(mid, parent_model, color, left_model, right_model, old(up.model))
                                                                == ctx_concat(erase_context(mu), Context::Left(rid, mid, rc, rr,
                                                                    Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)))) by {
                                                                unfold(rb_successor_context(mid, parent_model, color, left_model, right_model, old(up.model)));
                                                                rewrite(right_model, RbTree::Node(rid, rp, rc, rl, rr));
                                                                unfold(rb_reparent(RbTree::Node(rid, rp, rc, rl, rr), mid));
                                                                rewrite(rb_min_context(RbTree::Node(rid, mid, rc, rl, rr),
                                                                    Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model))), rb_min_context(rl, Context::Left(rid, mid, rc, rr,
                                                                        Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)))));
                                                                rewrite(rl, plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr)));
                                                                rewrite(rb_min_context(plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr)),
                                                                    Context::Left(rid, mid, rc, rr, Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)))), rb_min_context(RbTree::Node(mid, mp, mc, RbTree::Empty, mr),
                                                                        ctx_concat(erase_context(mu), Context::Left(rid, mid, rc, rr, Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model))))));
                                                                unfold(rb_min_context(RbTree::Node(mid, mp, mc, RbTree::Empty, mr),
                                                                    ctx_concat(erase_context(mu), Context::Left(rid, mid, rc, rr, Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)))))); normalize();
                                                            }
                                                            have deficit.model == rb_successor_context(mid, parent_model, color, left_model, right_model, old(up.model)) by {
                                                                rewrite(rb_successor_context(mid, parent_model, color, left_model, right_model, old(up.model)), ctx_concat(erase_context(mu), Context::Left(rid, mid, rc, rr,
                                                                        Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model))))); close();
                                                            }
                                                            have deficit.model == erase_deep_context(old(tree.model), old(up.model)) by {
                                                                rewrite(old(tree.model), RbTree::Node(identity, parent_model, color, left_model, right_model));
                                                                unfold(erase_deep_context(RbTree::Node(identity, parent_model, color, left_model, right_model), old(up.model)));
                                                                rewrite(erase_minimum_identity(rb_minimum(right_model)), mid); close();
                                                            }
                                                            have ctx_rb(deficit.model, Nat::Succ(Nat::Zero), Color::Black) == 1 by {
                                                                rewrite(deficit.model, rb_successor_context(mid, parent_model, color, left_model, right_model, old(up.model))); close();
                                                            }
                                                            have ctx_consistent(deficit.model, hole.model, 0) == 1 by {
                                                                rewrite(hole.model, RbTree::Empty);
                                                                rewrite(deficit.model, rb_successor_context(mid, parent_model, color, left_model, right_model, old(up.model))); close();
                                                            }
                                                            have plug(deficit.model, hole.model) == plug(old(up.model), erase_deep_model(old(tree.model))) by {
                                                                rewrite(hole.model, RbTree::Empty);
                                                                rewrite(old(tree.model), RbTree::Node(identity, parent_model, color, left_model, right_model));
                                                                unfold(erase_deep_model(RbTree::Node(identity, parent_model, color, left_model, right_model)));
                                                                rewrite(erase_minimum_identity(rb_minimum(right_model)), mid);
                                                                rewrite(deficit.model, rb_successor_context(mid, parent_model, color, left_model, right_model, old(up.model))); close();
                                                            }
                                                            have rb_inorder(erase_deep_model(old(tree.model))) == list::append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model)))) by {
                                                                rewrite(old(tree.model), RbTree::Node(identity, parent_model, color, left_model, right_model));
                                                                unfold(erase_deep_model(RbTree::Node(identity, parent_model, color, left_model, right_model)));
                                                                unfold(rb_left(RbTree::Node(identity, parent_model, color, left_model, right_model)));
                                                                unfold(rb_right(RbTree::Node(identity, parent_model, color, left_model, right_model)));
                                                                rewrite(erase_minimum_identity(rb_minimum(right_model)), mid); close();
                                                            }
                                                            apply(erase_spine_context_parent(mu, rid, mid, rc, rr, Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model))));
                                                            have ctx_node_is(deficit.model, rebalance) == 1 by {
                                                                rewrite(deficit.model, ctx_concat(erase_context(mu), Context::Left(rid, mid, rc, rr, Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)))));
                                                                rewrite(rebalance, mp); rewrite(mp, erase_spine_parent(mu, rid)); close();
                                                            }
                                                            have deficit.model != Context::Top by {
                                                                if deficit.model == Context::Top {
                                                                    have ctx_node_is(Context::Top, rebalance) == 1 by { rewrite(Context::Top, deficit.model); close(); }
                                                                    have rebalance != 0;
                                                                    have ctx_node_is(Context::Top, rebalance) != 1 by {
                                                                        unfold(ctx_node_is(Context::Top, rebalance)); normalize() using { not(rebalance == 0); };
                                                                    }
                                                                    contradiction(ctx_node_is(Context::Top, rebalance) == 1);
                                                                } else { close(); }
                                                            }
                                                            have ctx_consistent(erase_deep_context(old(tree.model), old(up.model)), RbTree::Empty, 0) == 1 by {
                                                                rewrite(erase_deep_context(old(tree.model), old(up.model)), deficit.model); rewrite(RbTree::Empty, hole.model); close();
                                                            }
                                                            apply(plug_parent_consistent_transport(erase_deep_context(old(tree.model), old(up.model)), RbTree::Empty, 0));
                                                            have rb_tree_parent_consistent(plug(erase_deep_context(old(tree.model), old(up.model)), RbTree::Empty)) == 1 by {
                                                                unfold(rb_tree_parent_consistent(plug(erase_deep_context(old(tree.model), old(up.model)), RbTree::Empty)));
                                                            }
                                                            apply(erase_outcome_deep(identity, parent_model, color, lid, lp, lc, ll, lr, rid, rp, rc, iid, ip, ic, il, ir, rr, old(up.model)));
                                                            have old(tree.model) == RbTree::Node(identity, parent_model, color, RbTree::Node(lid, lp, lc, ll, lr), RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr)) by {
                                                                rewrite(old(tree.model), RbTree::Node(identity, parent_model, color, left_model, right_model));
                                                                rewrite(left_model, RbTree::Node(lid, lp, lc, ll, lr));
                                                                rewrite(right_model, RbTree::Node(rid, rp, rc, rl, rr));
                                                                rewrite(rl, RbTree::Node(iid, ip, ic, il, ir)); normalize();
                                                            }
                                                            have rb_minimum(RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr)) == RbMinimum::Found(mid, Color::Black, RbTree::Empty) by {
                                                                rewrite(RbTree::Node(iid, ip, ic, il, ir), rl);
                                                                rewrite(RbTree::Node(rid, rp, rc, rl, rr), right_model); close();
                                                            }
                                                            have erase_outcome(old(tree.model), old(up.model)) == EraseOutcome::Deficit(erase_deep_context(old(tree.model), old(up.model))) by {
                                                                rewrite(old(tree.model), RbTree::Node(identity, parent_model, color, RbTree::Node(lid, lp, lc, ll, lr), RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr)));
                                                                rewrite(erase_outcome(RbTree::Node(identity, parent_model, color, RbTree::Node(lid, lp, lc, ll, lr), RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr)), old(up.model)), erase_deep_outcome(RbTree::Node(identity, parent_model, color, RbTree::Node(lid, lp, lc, ll, lr), RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr)), old(up.model), rb_minimum(RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr))));
                                                                rewrite(rb_minimum(RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr)), RbMinimum::Found(mid, Color::Black, RbTree::Empty));
                                                                unfold(erase_deep_outcome(RbTree::Node(identity, parent_model, color, RbTree::Node(lid, lp, lc, ll, lr), RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr)), old(up.model), RbMinimum::Found(mid, Color::Black, RbTree::Empty)));
                                                                normalize();
                                                            }
                                                            have erase_splice(old(tree.model)) == erase_deep_model(old(tree.model)) by {
                                                                rewrite(old(tree.model), RbTree::Node(identity, parent_model, color, RbTree::Node(lid, lp, lc, ll, lr), RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr)));
                                                                rewrite(erase_splice(RbTree::Node(identity, parent_model, color, RbTree::Node(lid, lp, lc, ll, lr), RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr))), erase_deep_splice(RbTree::Node(identity, parent_model, color, RbTree::Node(lid, lp, lc, ll, lr), RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr)), rb_minimum(RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr))));
                                                                rewrite(rb_minimum(RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr)), RbMinimum::Found(mid, Color::Black, RbTree::Empty));
                                                                unfold(erase_deep_splice(RbTree::Node(identity, parent_model, color, RbTree::Node(lid, lp, lc, ll, lr), RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr)), RbMinimum::Found(mid, Color::Black, RbTree::Empty)));
                                                                normalize();
                                                            }
                                                            have rb_inorder(erase_splice(old(tree.model))) == list::append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model)))) by {
                                                                rewrite(erase_splice(old(tree.model)), erase_deep_model(old(tree.model))); close();
                                                            }
                                                            unfold(hole);
                                                            with(erase_callbacks(augment)) { step_until(function.exit); }
                                                            have erase_deep_context(old(tree.model), old(up.model)) != Context::Top by {
                                                                rewrite(erase_deep_context(old(tree.model), old(up.model)), deficit.model); close();
                                                            }
                                                            have ctx_node_is(erase_deep_context(old(tree.model), old(up.model)), result) == 1 by {
                                                                rewrite(erase_deep_context(old(tree.model), old(up.model)), deficit.model); close();
                                                            }
                                                            let out = fold(erase_out(root, result), { model: EraseOutcome::Deficit(erase_deep_context(old(tree.model), old(up.model))), deficit: deficit });
                                                            have erase_out_rb(out.model) == 1 by {
                                                                rewrite(out.model, EraseOutcome::Deficit(erase_deep_context(old(tree.model), old(up.model))));
                                                                unfold(erase_out_rb(EraseOutcome::Deficit(erase_deep_context(old(tree.model), old(up.model))))); close();
                                                            }
                                                            have erase_out_tree(out.model) == plug(erase_deep_context(old(tree.model), old(up.model)), RbTree::Empty) by {
                                                                rewrite(out.model, EraseOutcome::Deficit(erase_deep_context(old(tree.model), old(up.model))));
                                                                unfold(erase_out_tree(EraseOutcome::Deficit(erase_deep_context(old(tree.model), old(up.model))))); normalize();
                                                            }
                                                            have rb_tree_parent_consistent(erase_out_tree(out.model)) == 1 by {
                                                                rewrite(erase_out_tree(out.model), plug(erase_deep_context(old(tree.model), old(up.model)), RbTree::Empty)); close();
                                                            }
                                                            close();
                                                        },
                                                    }
                                                },
                                            }
                                        },
                                    }
                                },
                            }
                        },
                    }
                },
            }
        } else {
            have not(erase_minimum_child(rb_minimum(rb_right(tree.model))) == RbTree::Empty)
                or erase_minimum_color(rb_minimum(rb_right(tree.model))) == Color::Red by {
                if erase_minimum_child(rb_minimum(rb_right(tree.model))) == RbTree::Empty {
                    have not(erase_minimum_color(rb_minimum(rb_right(tree.model))) == Color::Black) by {
                        if erase_minimum_color(rb_minimum(rb_right(tree.model))) == Color::Black {
                            have erase_minimum_child(rb_minimum(rb_right(tree.model))) == RbTree::Empty
                                and erase_minimum_color(rb_minimum(rb_right(tree.model))) == Color::Black by close();
                            contradiction(erase_minimum_child(rb_minimum(rb_right(tree.model))) == RbTree::Empty
                                and erase_minimum_color(rb_minimum(rb_right(tree.model))) == Color::Black);
                        } else {
                            close();
                        }
                    }
                    apply(erase_unlink_red_if_not_black(erase_minimum_color(rb_minimum(rb_right(tree.model)))));
                    close();
                } else {
                    close();
                }
            }
            match tree.model {
                RbTree::Empty => { contradiction(tree.model == RbTree::Empty); },
                RbTree::Node(identity, parent_model, color, left_model, right_model) => {
                    have rb_left(tree.model) == left_model by {
                        rewrite(tree.model, RbTree::Node(identity, parent_model, color, left_model, right_model));
                        unfold(rb_left(RbTree::Node(identity, parent_model, color, left_model, right_model))); normalize();
                    }
                    have rb_right(tree.model) == right_model by {
                        rewrite(tree.model, RbTree::Node(identity, parent_model, color, left_model, right_model));
                        unfold(rb_right(RbTree::Node(identity, parent_model, color, left_model, right_model))); normalize();
                    }
                    have left_model != RbTree::Empty by { rewrite(left_model, rb_left(tree.model)); close(); }
                    have right_model != RbTree::Empty by { rewrite(right_model, rb_right(tree.model)); close(); }
                    have not(erase_minimum_child(rb_minimum(right_model)) == RbTree::Empty)
                        or erase_minimum_color(rb_minimum(right_model)) == Color::Red by {
                        rewrite(right_model, rb_right(tree.model)); close();
                    }
                    have rb_left(right_model) != RbTree::Empty by { rewrite(right_model, rb_right(tree.model)); close(); }
                    apply(erase_context_parent(up.model, identity, parent_model, color, left_model, right_model));
                    apply(ctx_consistent_node_children(up.model, identity, parent_model, color, left_model, right_model, 0));
                    have is_rb(RbTree::Node(identity, parent_model, color, left_model, right_model)) == 1 by {
                        rewrite(RbTree::Node(identity, parent_model, color, left_model, right_model), tree.model); close();
                    }
                    have ctx_rb(up.model, black_height(RbTree::Node(identity, parent_model, color, left_model, right_model)), rb_color(RbTree::Node(identity, parent_model, color, left_model, right_model))) == 1 by {
                        rewrite(RbTree::Node(identity, parent_model, color, left_model, right_model), tree.model); close();
                    }
                    let { left: l, right: r } = unfold(tree);
                    mark erased_parent_initial;
                    let old_left = fold(erase_saved_left(node), { child: node->rb_left });
                    match left_model {
                        RbTree::Empty => { contradiction(left_model == RbTree::Empty); },
                        RbTree::Node(lid, lp, lc, ll, lr) => {
                            let { left: ll_tree, right: lr_tree } = unfold(l);
                            let left_color = fold(erase_saved_color(lid), { color: lc });
                            mark before_left_splice;
                            let left_children = fold(erase_saved_children(lid), {
                                left: lid->rb_left, right: lid->rb_right
                            });
                            match right_model {
                                RbTree::Empty => { contradiction(right_model == RbTree::Empty); },
                                RbTree::Node(rid, rp, rc, rl, rr) => {
                                    have rl != RbTree::Empty by {
                                        unfold(rb_left(RbTree::Node(rid, rp, rc, rl, rr)));
                                        rewrite(rl, rb_left(RbTree::Node(rid, rp, rc, rl, rr)));
                                        rewrite(RbTree::Node(rid, rp, rc, rl, rr), right_model); close();
                                    }
                                    apply(rb_parent_consistent_node_left(rid, rp, rc, rl, rr, identity));
                                    apply(rb_remove_min_blackened_parent_consistent(rl, rid));
                                    let { left: t, right: right_sibling } = unfold(r);
                                    match rl {
                                        RbTree::Empty => { contradiction(rl == RbTree::Empty); },
                                        RbTree::Node(iid, ip, ic, il, ir) => {
                                            let { left: init_l, right: init_r } = unfold(t);
                                            let t = fold(rb_at(iid), { model: RbTree::Node(iid, ip, ic, il, ir), left: init_l, right: init_r });
                                            step(); step(); step(); step(); step(); step(); step(); step(); step(); step(); step(); step(); step(); step();
                                            let c = fold(erase_spine_at(tmp, child), { model: EraseSpine::Top });
                                            have plug(erase_context(c.model), t.model) == rl by {
                                                rewrite(c.model, EraseSpine::Top);
                                                unfold(erase_context(EraseSpine::Top));
                                                unfold(plug(Context::Top, t.model)); close();
                                            }
                                            have successor == erase_spine_parent(c.model, child) by {
                                                rewrite(c.model, EraseSpine::Top);
                                                unfold(erase_spine_parent(EraseSpine::Top, child)); close();
                                            }
                                            loop {
                                                owns c: erase_spine_at(tmp, child);
                                                owns t: rb_at(tmp);
                                                decreases t;
                                                invariant tmp != 0;
                                                invariant successor == erase_spine_parent(c.model, child);
                                                invariant plug(erase_context(c.model), t.model) == rl;
                                                initialize by close();
                                                maintain by {
                                                    match t.model {
                                                        RbTree::Empty => { unfold(t); have tmp != 0 by { close(); } contradiction(tmp == 0); },
                                                        RbTree::Node(tid, tp, tc, tl, tr) => {
                                                            have plug(erase_context(EraseSpine::Left(tid, tp, tc, tr, c.model)), tl) == rl by {
                                                                unfold(erase_context(EraseSpine::Left(tid, tp, tc, tr, c.model)));
                                                                unfold(plug(Context::Left(tid, tp, tc, tr, erase_context(c.model)), tl));
                                                                rewrite(RbTree::Node(tid, tp, tc, tl, tr), t.model); close();
                                                            }
                                                            mark before_spine_unfold;
                                                            let { left: next, right: sibling } = unfold(t);
                                                            have tmp->rb_right == at(before_spine_unfold, tmp->rb_right) by close();
                                                            have tmp == tid by close();
                                                            have tid != 0 by { rewrite(tid, tmp); close(); }
                                                            have erase_spine_parent(EraseSpine::Left(tid, tp, tc, tr, c.model), child) == tid by {
                                                                unfold(erase_spine_parent(EraseSpine::Left(tid, tp, tc, tr, c.model), child)); normalize();
                                                            }
                                                            let frame = fold(erase_spine_at(tmp->rb_left, child),
                                                                { model: EraseSpine::Left(tmp, tp, tc, tr, c.model), up: c, sibling: sibling });
                                                            step(); step(); step();
                                                            if tmp == 0 {
                                                            } else {
                                                            }
                                                        },
                                                    }
                                                }
                                            }
                                            match t.model {
                                                RbTree::Node(a, b, col, lt, rt) => {
                                                    have t.model == RbTree::Empty by close();
                                                    have t.model != RbTree::Empty by { rewrite(t.model, RbTree::Node(a, b, col, lt, rt)); normalize(); }
                                                    contradiction(t.model == RbTree::Empty);
                                                },
                                                RbTree::Empty => {
                                                    have c.model != EraseSpine::Top by normalize();
                                                    match c.model {
                                                        EraseSpine::Top => { contradiction(c.model == EraseSpine::Top); },
                                                        EraseSpine::Left(mid, mp, mc, mr, mu) => {
                                                            apply(erase_spine_minimum(mu, RbTree::Node(mid, mp, mc, RbTree::Empty, mr)));
                                                            have rb_minimum(rl) == RbMinimum::Found(mid, mc, mr) by {
                                                                rewrite(rl, plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr)));
                                                                rewrite(rb_minimum(plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr))), rb_minimum(RbTree::Node(mid, mp, mc, RbTree::Empty, mr)));
                                                                unfold(rb_minimum(RbTree::Node(mid, mp, mc, RbTree::Empty, mr))); normalize();
                                                            }
                                                            apply(rb_minimum_nonempty_left(rid, rp, rc, rl, rr));
                                                            have rb_minimum(right_model) == RbMinimum::Found(mid, mc, mr) by {
                                                                rewrite(right_model, RbTree::Node(rid, rp, rc, rl, rr));
                                                                rewrite(rb_minimum(RbTree::Node(rid, rp, rc, rl, rr)), rb_minimum(rl)); close();
                                                            }
                                                            have not(mr == RbTree::Empty) or mc == Color::Red by {
                                                                have erase_minimum_child(rb_minimum(right_model)) == mr by {
                                                                    rewrite(rb_minimum(right_model), RbMinimum::Found(mid, mc, mr));
                                                                    unfold(erase_minimum_child(RbMinimum::Found(mid, mc, mr))); normalize();
                                                                }
                                                                have erase_minimum_color(rb_minimum(right_model)) == mc by {
                                                                    rewrite(rb_minimum(right_model), RbMinimum::Found(mid, mc, mr));
                                                                    unfold(erase_minimum_color(RbMinimum::Found(mid, mc, mr))); normalize();
                                                                }
                                                                rewrite(mr, erase_minimum_child(rb_minimum(right_model)));
                                                                rewrite(mc, erase_minimum_color(rb_minimum(right_model))); close();
                                                            }
                                                            apply(rb_erase_no_fixup_successor_splice(identity, mid, parent_model, color,
                                                                left_model, right_model, up.model, 0, mc, mr));
                                                            apply(rb_remove_min_blackened_nonempty_left(rid, rp, rc, rl, rr));
                                                            have erase_minimum_identity(rb_minimum(right_model)) == mid by {
                                                                rewrite(rb_minimum(right_model), RbMinimum::Found(mid, mc, mr));
                                                                unfold(erase_minimum_identity(RbMinimum::Found(mid, mc, mr))); normalize();
                                                            }
                                                            apply(erase_spine_focus_parent_consistent(mu, RbTree::Node(mid, mp, mc, RbTree::Empty, mr), rid));
                                                            apply(erase_parent_consistent_parent_is(RbTree::Node(mid, mp, mc, RbTree::Empty, mr), erase_spine_parent(mu, rid)));
                                                            apply(rb_parent_is_node_parent(mid, mp, mc, RbTree::Empty, mr, erase_spine_parent(mu, rid)));
                                                            apply(erase_spine_remove_min_blackened(mu, RbTree::Node(mid, mp, mc, RbTree::Empty, mr)));
                                                            have rb_remove_min_blackened(rl) == plug(erase_context(mu), rb_reparent(rb_recolor(mr, Color::Black), mp)) by {
                                                                rewrite(rl, plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr)));
                                                                rewrite(rb_remove_min_blackened(plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr))), plug(erase_context(mu), rb_remove_min_blackened(RbTree::Node(mid, mp, mc, RbTree::Empty, mr))));
                                                                unfold(rb_remove_min_blackened(RbTree::Node(mid, mp, mc, RbTree::Empty, mr))); normalize();
                                                            }
                                                            let { sibling: min_right, up: path } = unfold(c);
                                                            have (mid->__rb_parent_color & 1) == color_bit(mc) by close();
                                                            let successor_color = fold(erase_saved_color(mid), { color: mc });
                                                            unfold(t);
                                                            have parent == erase_spine_parent(path.model, child);
                                                            have parent == mp by {
                                                                rewrite(parent, erase_spine_parent(path.model, child));
                                                                rewrite(path.model, mu); rewrite(child, rid);
                                                                rewrite(erase_spine_parent(mu, rid), mp); normalize();
                                                            }
                                                            have path.model == mu;
                                                            mark opened_spine;
                                                            let { frame: link_frame } = open_erase_spine_link(successor, parent, child, { c: path });
                                                            have link_frame.model == at(opened_spine, path.model) by close();
                                                            let saved_color = fold(erase_saved_color(child), { color: rc });
                                                            step(); // Read the successor’s right child.
                                                            mark before_detaching_successor;
                                                            have *((&node->__rb_parent_color) as (int32**)) == at(erased_parent_initial, *((&node->__rb_parent_color) as (int32**))) by close();
                                                            have separate(memory(parent->rb_left), memory(node->__rb_parent_color)) by close();
                                                            step();
                                                            mark after_detaching_successor;
                                                            have separate(region(36).footprint, memory(node->__rb_parent_color)) by {
                                                                normalize() using { separate(memory(parent->rb_left), memory(node->__rb_parent_color)); };
                                                            }
                                                            have *((&node->__rb_parent_color) as (int32**)) == at(before_detaching_successor, *((&node->__rb_parent_color) as (int32**))) by {
                                                                preserve(memory(node->__rb_parent_color), region(36));
                                                            }
                                                            have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == parent_model by close();
                                                            mark before_linking_successor;
                                                            have separate(memory(successor->rb_right), memory(node->__rb_parent_color)) by close();
                                                            step();
                                                            mark after_linking_successor;
                                                            have separate(region(37).footprint, memory(node->__rb_parent_color)) by {
                                                                normalize() using { separate(memory(successor->rb_right), memory(node->__rb_parent_color)); };
                                                            }
                                                            have *((&node->__rb_parent_color) as (int32**)) == at(before_linking_successor, *((&node->__rb_parent_color) as (int32**))) by {
                                                                preserve(memory(node->__rb_parent_color), region(37));
                                                            }
                                                            have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == parent_model by close();
                                                            unfold(saved_color);
                                                            have (child->__rb_parent_color & 1) == color_bit(rc) by close();
                                                            mark before_reparent;
                                                            have separate(memory(child->__rb_parent_color), memory(node->__rb_parent_color)) by close();
                                                            step();
                                                            mark after_child_reparent;
                                                            have contains(memory(child->__rb_parent_color), region(38).footprint) by close();
                                                            apply(click::separation::contains_refl(memory(node->__rb_parent_color)));
                                                            apply(click::separation::separate_restrict(memory(child->__rb_parent_color), memory(node->__rb_parent_color), region(38).footprint, memory(node->__rb_parent_color)));
                                                            have *((&node->__rb_parent_color) as (int32**)) == at(before_reparent, *((&node->__rb_parent_color) as (int32**))) by {
                                                                preserve(memory(node->__rb_parent_color), region(38));
                                                            }
                                                            have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == parent_model by close();
                                                            apply(packed_parent_word(successor, at(before_reparent, child->__rb_parent_color)));
                                                            have child->__rb_parent_color == address(mid) + (child->__rb_parent_color & 1) by {
                                                                rewrite(child->__rb_parent_color, ((at(before_reparent, child->__rb_parent_color) & 1) | address(successor)));
                                                                rewrite(mid, successor);
                                                                close();
                                                            }
                                                            have (child->__rb_parent_color & 1) == (at(before_reparent, child->__rb_parent_color) & 1) by {
                                                                rewrite(child->__rb_parent_color, ((at(before_reparent, child->__rb_parent_color) & 1) | address(successor)));
                                                                close();
                                                            }
                                                            have (child->__rb_parent_color & 1) == color_bit(rc) by {
                                                                rewrite((child->__rb_parent_color & 1), (at(before_reparent, child->__rb_parent_color) & 1));
                                                                close();
                                                            }
                                                            with(erase_callbacks(augment)) {
                                                                mark before_copy;
                                                                step();
                                                                have separate(region(39).footprint, memory(node->__rb_parent_color)) by {
                                                                    normalize() using { };
                                                                }
                                                                have *((&node->__rb_parent_color) as (int32**)) == at(before_copy, *((&node->__rb_parent_color) as (int32**))) by {
                                                                    preserve(memory(node->__rb_parent_color), region(39));
                                                                }
                                                                have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == parent_model by close();
                                                                mark before_propagate;
                                                                step();
                                                                have separate(region(40).footprint, memory(node->__rb_parent_color)) by {
                                                                    normalize() using { };
                                                                }
                                                                have *((&node->__rb_parent_color) as (int32**)) == at(before_propagate, *((&node->__rb_parent_color) as (int32**))) by {
                                                                    preserve(memory(node->__rb_parent_color), region(40));
                                                                }
                                                                have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == parent_model by close();
                                                            }
                                                            have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == parent_model by close();
                                                            unfold(old_left);
                                                            have node->rb_left == lid by close();
                                                            mark before_reading_left_child;
                                                            step();
                                                            have separate(region(41).footprint, memory(node->__rb_parent_color)) by {
                                                                normalize() using { };
                                                            }
                                                            have *((&node->__rb_parent_color) as (int32**)) == at(before_reading_left_child, *((&node->__rb_parent_color) as (int32**))) by {
                                                                preserve(memory(node->__rb_parent_color), region(41));
                                                            }
                                                            have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == parent_model by close();
                                                            mark before_linking_left_child;
                                                            have separate(memory(successor->rb_left), memory(node->__rb_parent_color)) by close();
                                                            step();
                                                            mark after_linking_left_child;
                                                            have separate(region(42).footprint, memory(node->__rb_parent_color)) by {
                                                                normalize() using { separate(memory(successor->rb_left), memory(node->__rb_parent_color)); };
                                                            }
                                                            have *((&node->__rb_parent_color) as (int32**)) == at(before_linking_left_child, *((&node->__rb_parent_color) as (int32**))) by {
                                                                preserve(memory(node->__rb_parent_color), region(42));
                                                            }
                                                            have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == parent_model by close();
                                                            unfold(left_color);
                                                            have (tmp->__rb_parent_color & 1) == color_bit(lc) by close();
                                                            // Rebind tag ownership to the live C argument.
                                                            let live_left_tag = fold(erase_saved_color(tmp), { color: lc });
                                                            unfold(live_left_tag);
                                                            have separate(memory(tmp->__rb_parent_color), memory(*augment)) by close();
                                                            mark before_left_reparent;
                                                            step();
                                                            mark after_left_reparent;
                                                            have separate(at(before_left_reparent, memory(tmp->__rb_parent_color)), memory(node->__rb_parent_color)) by close();
                                                            have separate(region(43).footprint, memory(node->__rb_parent_color)) by {
                                                                normalize() using { separate(at(before_left_reparent, memory(tmp->__rb_parent_color)), memory(node->__rb_parent_color)); };
                                                            }
                                                            have *((&node->__rb_parent_color) as (int32**)) == at(before_left_reparent, *((&node->__rb_parent_color) as (int32**))) by {
                                                                preserve(memory(node->__rb_parent_color), region(43));
                                                            }
                                                            have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == parent_model by close();
                                                            have contains(at(before_left_reparent, memory(tmp->__rb_parent_color)), region(43).footprint) by close();
                                                            have separate(at(before_left_reparent, memory(tmp->__rb_parent_color)), memory(successor->rb_left)) by close();
                                                            apply(click::separation::contains_refl(memory(successor->rb_left)));
                                                            apply(click::separation::separate_restrict(at(before_left_reparent, memory(tmp->__rb_parent_color)), memory(successor->rb_left), region(43).footprint, memory(successor->rb_left)));
                                                            have at(after_linking_left_child, successor->rb_left) == lid by close();
                                                            have at(before_left_reparent, successor->rb_left) == at(after_linking_left_child, successor->rb_left) by close();
                                                            have successor->rb_left == at(before_left_reparent, successor->rb_left) by {
                                                                preserve(memory(successor->rb_left), region(43));
                                                            }
                                                            have successor->rb_left == lid by close();
                                                            have separate(memory(successor->rb_left), memory(child->__rb_parent_color)) by close();
                                                            have separate(memory(successor->rb_left), memory(parent->rb_left)) by close();
                                                            have separate(memory(child->rb_right), memory(successor->rb_left)) by close();
                                                            have at(before_detaching_successor, child->rb_right) == at(erased_parent_initial, node->rb_right->rb_right) by close();
                                                            have separate(memory(parent->rb_left), memory(child->rb_right)) by close();
                                                            have separate(region(36).footprint, memory(child->rb_right)) by {
                                                                normalize() using { separate(memory(parent->rb_left), memory(child->rb_right)); };
                                                            }
                                                            have at(after_detaching_successor, child->rb_right) == at(before_detaching_successor, child->rb_right) by {
                                                                preserve(memory(child->rb_right), region(36));
                                                            }
                                                            have at(after_detaching_successor, child->rb_right) == at(erased_parent_initial, node->rb_right->rb_right) by close();
                                                            have at(before_linking_successor, child->rb_right) == at(after_detaching_successor, child->rb_right) by close();
                                                            have separate(memory(successor->rb_right), memory(child->rb_right)) by close();
                                                            have separate(region(37).footprint, memory(child->rb_right)) by {
                                                                normalize() using { separate(memory(successor->rb_right), memory(child->rb_right)); };
                                                            }
                                                            have at(after_linking_successor, child->rb_right) == at(before_linking_successor, child->rb_right) by {
                                                                preserve(memory(child->rb_right), region(37));
                                                            }
                                                            have at(after_linking_successor, child->rb_right) == at(erased_parent_initial, node->rb_right->rb_right) by close();
                                                            have at(before_reparent, child->rb_right) == at(after_linking_successor, child->rb_right) by close();
                                                            have separate(memory(child->__rb_parent_color), memory(child->rb_right)) by { normalize() using { }; }
                                                            have separate(region(38).footprint, memory(child->rb_right)) by {
                                                                normalize() using { separate(memory(child->__rb_parent_color), memory(child->rb_right)); };
                                                            }
                                                            have at(after_child_reparent, child->rb_right) == at(before_reparent, child->rb_right) by {
                                                                preserve(memory(child->rb_right), region(38));
                                                            }
                                                            have at(after_child_reparent, child->rb_right) == at(erased_parent_initial, node->rb_right->rb_right) by close();
                                                            have at(before_copy, child->rb_right) == at(after_child_reparent, child->rb_right) by close();
                                                            have separate(region(39).footprint, memory(child->rb_right)) by {
                                                                normalize() using { };
                                                            }
                                                            have at(before_propagate, child->rb_right) == at(before_copy, child->rb_right) by {
                                                                preserve(memory(child->rb_right), region(39));
                                                            }
                                                            have at(before_propagate, child->rb_right) == at(erased_parent_initial, node->rb_right->rb_right) by close();
                                                            have separate(region(40).footprint, memory(child->rb_right)) by {
                                                                normalize() using { };
                                                            }
                                                            have at(before_reading_left_child, child->rb_right) == at(before_propagate, child->rb_right) by {
                                                                preserve(memory(child->rb_right), region(40));
                                                            }
                                                            have at(before_reading_left_child, child->rb_right) == at(erased_parent_initial, node->rb_right->rb_right) by close();
                                                            have separate(region(41).footprint, memory(child->rb_right)) by {
                                                                normalize() using { };
                                                            }
                                                            have at(before_linking_left_child, child->rb_right) == at(before_reading_left_child, child->rb_right) by {
                                                                preserve(memory(child->rb_right), region(41));
                                                            }
                                                            have at(before_linking_left_child, child->rb_right) == at(erased_parent_initial, node->rb_right->rb_right) by close();
                                                            have separate(memory(successor->rb_left), memory(child->rb_right)) by close();
                                                            have separate(region(42).footprint, memory(child->rb_right)) by {
                                                                normalize() using { separate(memory(successor->rb_left), memory(child->rb_right)); };
                                                            }
                                                            have at(after_linking_left_child, child->rb_right) == at(before_linking_left_child, child->rb_right) by {
                                                                preserve(memory(child->rb_right), region(42));
                                                            }
                                                            have at(after_linking_left_child, child->rb_right) == at(erased_parent_initial, node->rb_right->rb_right) by close();
                                                            have at(before_left_reparent, child->rb_right) == at(after_linking_left_child, child->rb_right) by close();
                                                            have separate(at(before_left_reparent, memory(tmp->__rb_parent_color)), memory(child->rb_right)) by close();
                                                            apply(click::separation::contains_refl(memory(child->rb_right)));
                                                            apply(click::separation::separate_restrict(at(before_left_reparent, memory(tmp->__rb_parent_color)), memory(child->rb_right), region(43).footprint, memory(child->rb_right)));
                                                            have at(after_left_reparent, child->rb_right) == at(before_left_reparent, child->rb_right) by {
                                                                preserve(memory(child->rb_right), region(43));
                                                            }
                                                            have at(after_left_reparent, child->rb_right) == at(erased_parent_initial, node->rb_right->rb_right) by close();
                                                            have aligned(successor, 8) by close();
                                                            have aligned(successor, 8) implies at(after_child_reparent, ((child->__rb_parent_color & ~3) as (struct rb_node *))) == successor by close();
                                                            have at(after_child_reparent, ((child->__rb_parent_color & ~3) as (struct rb_node *))) == successor by {
                                                                close() using {
                                                                    aligned(successor, 8);
                                                                    aligned(successor, 8) implies at(after_child_reparent, ((child->__rb_parent_color & ~3) as (struct rb_node *))) == successor;
                                                                };
                                                            }
                                                            have at(before_copy, *((&child->__rb_parent_color) as (int32**))) == at(after_child_reparent, *((&child->__rb_parent_color) as (int32**))) by close();
                                                            have separate(region(39).footprint, memory(child->__rb_parent_color)) by {
                                                                normalize() using { };
                                                            }
                                                            have at(before_propagate, *((&child->__rb_parent_color) as (int32**))) == at(before_copy, *((&child->__rb_parent_color) as (int32**))) by {
                                                                preserve(memory(child->__rb_parent_color), region(39));
                                                            }
                                                            have at(before_propagate, *((&child->__rb_parent_color) as (int32**))) == at(after_child_reparent, *((&child->__rb_parent_color) as (int32**))) by close();
                                                            have at(before_propagate, ((child->__rb_parent_color & ~3) as (struct rb_node *))) == successor by close();
                                                            have separate(region(40).footprint, memory(child->__rb_parent_color)) by {
                                                                normalize() using { };
                                                            }
                                                            have at(before_reading_left_child, *((&child->__rb_parent_color) as (int32**))) == at(before_propagate, *((&child->__rb_parent_color) as (int32**))) by {
                                                                preserve(memory(child->__rb_parent_color), region(40));
                                                            }
                                                            have at(before_reading_left_child, *((&child->__rb_parent_color) as (int32**))) == at(after_child_reparent, *((&child->__rb_parent_color) as (int32**))) by close();
                                                            have at(before_reading_left_child, ((child->__rb_parent_color & ~3) as (struct rb_node *))) == successor by close();
                                                            have separate(region(41).footprint, memory(child->__rb_parent_color)) by {
                                                                normalize() using { };
                                                            }
                                                            have at(before_linking_left_child, *((&child->__rb_parent_color) as (int32**))) == at(before_reading_left_child, *((&child->__rb_parent_color) as (int32**))) by {
                                                                preserve(memory(child->__rb_parent_color), region(41));
                                                            }
                                                            have at(before_linking_left_child, *((&child->__rb_parent_color) as (int32**))) == at(after_child_reparent, *((&child->__rb_parent_color) as (int32**))) by close();
                                                            have at(before_linking_left_child, ((child->__rb_parent_color & ~3) as (struct rb_node *))) == successor by close();
                                                            have separate(memory(successor->rb_left), memory(child->__rb_parent_color)) by close();
                                                            have separate(region(42).footprint, memory(child->__rb_parent_color)) by {
                                                                normalize() using { separate(memory(successor->rb_left), memory(child->__rb_parent_color)); };
                                                            }
                                                            have at(after_linking_left_child, *((&child->__rb_parent_color) as (int32**))) == at(before_linking_left_child, *((&child->__rb_parent_color) as (int32**))) by {
                                                                preserve(memory(child->__rb_parent_color), region(42));
                                                            }
                                                            have at(after_linking_left_child, *((&child->__rb_parent_color) as (int32**))) == at(after_child_reparent, *((&child->__rb_parent_color) as (int32**))) by close();
                                                            have at(after_linking_left_child, child->__rb_parent_color) == at(before_linking_left_child, child->__rb_parent_color) by {
                                                                preserve(memory(child->__rb_parent_color), region(42));
                                                            }
                                                            have at(after_linking_left_child, ((child->__rb_parent_color & ~3) as (struct rb_node *))) == successor by {
                                                                rewrite(at(after_linking_left_child, child->__rb_parent_color), at(before_linking_left_child, child->__rb_parent_color));
                                                                close();
                                                            }
                                                            have at(before_left_reparent, *((&child->__rb_parent_color) as (int32**))) == at(after_linking_left_child, *((&child->__rb_parent_color) as (int32**))) by close();
                                                            have separate(at(before_left_reparent, memory(tmp->__rb_parent_color)), memory(child->__rb_parent_color)) by close();
                                                            apply(click::separation::contains_refl(memory(child->__rb_parent_color)));
                                                            apply(click::separation::separate_restrict(at(before_left_reparent, memory(tmp->__rb_parent_color)), memory(child->__rb_parent_color), region(43).footprint, memory(child->__rb_parent_color)));
                                                            have *((&child->__rb_parent_color) as (int32**)) == at(before_left_reparent, *((&child->__rb_parent_color) as (int32**))) by {
                                                                preserve(memory(child->__rb_parent_color), region(43));
                                                            }
                                                            have *((&child->__rb_parent_color) as (int32**)) == at(after_child_reparent, *((&child->__rb_parent_color) as (int32**))) by close();
                                                            have at(before_left_reparent, child->__rb_parent_color) == at(after_linking_left_child, child->__rb_parent_color) by close();
                                                            have at(before_left_reparent, ((child->__rb_parent_color & ~3) as (struct rb_node *))) == successor by close();
                                                            have child->__rb_parent_color == at(before_left_reparent, child->__rb_parent_color) by {
                                                                preserve(memory(child->__rb_parent_color), region(43));
                                                            }
                                                            have ((child->__rb_parent_color & ~3) as (struct rb_node *)) == successor by {
                                                                rewrite(child->__rb_parent_color, at(before_left_reparent, child->__rb_parent_color));
                                                                close();
                                                            }
                                                            let transplanted_left = fold(erase_saved_left(successor), { child: lid });
                                                            have at(after_linking_successor, successor->rb_right) == child by close();
                                                            have at(before_reparent, successor->rb_right) == at(after_linking_successor, successor->rb_right) by close();
                                                            have separate(memory(child->__rb_parent_color), memory(successor->rb_right)) by close();
                                                            have separate(region(38).footprint, memory(successor->rb_right)) by {
                                                                normalize() using { separate(memory(child->__rb_parent_color), memory(successor->rb_right)); };
                                                            }
                                                            have at(after_child_reparent, successor->rb_right) == at(before_reparent, successor->rb_right) by {
                                                                preserve(memory(successor->rb_right), region(38));
                                                            }
                                                            have at(after_child_reparent, successor->rb_right) == child by close();
                                                            have at(before_copy, successor->rb_right) == at(after_child_reparent, successor->rb_right) by close();
                                                            have separate(region(39).footprint, memory(successor->rb_right)) by {
                                                                normalize() using { };
                                                            }
                                                            have at(before_propagate, successor->rb_right) == at(before_copy, successor->rb_right) by {
                                                                preserve(memory(successor->rb_right), region(39));
                                                            }
                                                            have at(before_propagate, successor->rb_right) == child by close();
                                                            have separate(region(40).footprint, memory(successor->rb_right)) by {
                                                                normalize() using { };
                                                            }
                                                            have at(before_reading_left_child, successor->rb_right) == at(before_propagate, successor->rb_right) by {
                                                                preserve(memory(successor->rb_right), region(40));
                                                            }
                                                            have at(before_reading_left_child, successor->rb_right) == child by close();
                                                            have separate(region(41).footprint, memory(successor->rb_right)) by {
                                                                normalize() using { };
                                                            }
                                                            have at(before_linking_left_child, successor->rb_right) == at(before_reading_left_child, successor->rb_right) by {
                                                                preserve(memory(successor->rb_right), region(41));
                                                            }
                                                            have at(before_linking_left_child, successor->rb_right) == child by close();
                                                            have separate(memory(successor->rb_left), memory(successor->rb_right)) by { normalize() using { }; }
                                                            have separate(region(42).footprint, memory(successor->rb_right)) by {
                                                                normalize() using { separate(memory(successor->rb_left), memory(successor->rb_right)); };
                                                            }
                                                            have at(after_linking_left_child, successor->rb_right) == at(before_linking_left_child, successor->rb_right) by {
                                                                preserve(memory(successor->rb_right), region(42));
                                                            }
                                                            have at(after_linking_left_child, successor->rb_right) == child by close();
                                                            have at(before_left_reparent, successor->rb_right) == at(after_linking_left_child, successor->rb_right) by close();
                                                            have separate(at(before_left_reparent, memory(tmp->__rb_parent_color)), memory(successor->rb_right)) by close();
                                                            apply(click::separation::contains_refl(memory(successor->rb_right)));
                                                            apply(click::separation::separate_restrict(at(before_left_reparent, memory(tmp->__rb_parent_color)), memory(successor->rb_right), region(43).footprint, memory(successor->rb_right)));
                                                            have successor->rb_right == at(before_left_reparent, successor->rb_right) by {
                                                                preserve(memory(successor->rb_right), region(43));
                                                            }
                                                            have successor->rb_right == child by close();
                                                            have separate(memory(successor->rb_right), memory(parent->rb_left)) by close();
                                                            have separate(memory(child->rb_right), memory(successor->rb_right)) by close();
                                                            let transplanted_right = fold(erase_saved_right(successor), { child: child });
                                                            have separate(memory(child->__rb_parent_color), at(before_left_reparent, memory(tmp->__rb_parent_color))) by close();
                                                            have separate(memory(child->__rb_parent_color), memory(parent->rb_left)) by close();
                                                            have separate(memory(child->rb_right), memory(child->__rb_parent_color)) by close();
                                                            have ((child->__rb_parent_color & ~3) as (struct rb_node *)) == mid by {
                                                                rewrite(mid, successor); close();
                                                            }
                                                            let retained_anchor_tag = fold(erase_saved_parent(child, mid), {
                                                                word: child->__rb_parent_color, color: rc
                                                            });
                                                            have aligned(successor, 8) by close();
                                                            have ((tmp->__rb_parent_color & ~3) as (struct rb_node *)) == successor by {
                                                                close() using {
                                                                    aligned(successor, 8);
                                                                    aligned(successor, 8) implies ((tmp->__rb_parent_color & ~3) as (struct rb_node *)) == successor;
                                                                };
                                                            }
                                                            apply(packed_parent_word(successor, at(before_left_reparent, tmp->__rb_parent_color)));
                                                            have tmp->__rb_parent_color == address(successor) + (tmp->__rb_parent_color & 1) by {
                                                                rewrite(tmp->__rb_parent_color, ((at(before_left_reparent, tmp->__rb_parent_color) & 1) | address(successor)));
                                                                close();
                                                            }
                                                            have (tmp->__rb_parent_color & 1) == color_bit(lc) by {
                                                                rewrite(tmp->__rb_parent_color, ((at(before_left_reparent, tmp->__rb_parent_color) & 1) | address(successor)));
                                                                rewrite(((at(before_left_reparent, tmp->__rb_parent_color) & 1) | address(successor)) & 1,
                                                                    at(before_left_reparent, tmp->__rb_parent_color) & 1);
                                                                close();
                                                            }
                                                            let moved_parent = fold(erase_saved_parent(tmp, successor), {
                                                                word: tmp->__rb_parent_color, color: lc
                                                            });
                                                            unfold(left_children);
                                                            unfold(moved_parent);
                                                            have tmp->rb_left == at(before_left_splice, lid->rb_left) by close();
                                                            have tmp->rb_right == at(before_left_splice, lid->rb_right) by close();
                                                            let moved_left = fold(rb_at(tmp), {
                                                                model: RbTree::Node(lid, successor, lc, ll, lr),
                                                                left: ll_tree, right: lr_tree
                                                            });
                                                            have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == parent_model by close();
                                                            mark before_reading_packed_parent;
                                                            step();
                                                            have separate(region(44).footprint, memory(node->__rb_parent_color)) by {
                                                                normalize() using { };
                                                            }
                                                            have *((&node->__rb_parent_color) as (int32**)) == at(before_reading_packed_parent, *((&node->__rb_parent_color) as (int32**))) by {
                                                                preserve(memory(node->__rb_parent_color), region(44));
                                                            }
                                                            have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == parent_model by close();
                                                            have ((pc & ~3) as (struct rb_node *)) == parent_model by close();
                                                            step();
                                                            have separate(memory(child->rb_right), memory(lid->__rb_parent_color));
                                                            have separate(memory(child->rb_right), memory(node->__rb_parent_color));
                                                            have separate(memory(child->rb_right), memory(parent->rb_left));
                                                            have separate(memory(child->rb_right), memory(child->__rb_parent_color));
                                                            have moved_left.model == rb_reparent(left_model, mid) by {
                                                                rewrite(left_model, RbTree::Node(lid, lp, lc, ll, lr));
                                                                unfold(rb_reparent(RbTree::Node(lid, lp, lc, ll, lr), mid));
                                                                rewrite(successor, mid); normalize();
                                                            }
                                                            have tmp == parent_model;
                                                            have ctx_node_is(up.model, tmp) == 1 by {
                                                                rewrite(tmp, parent_model); close();
                                                            }

                                                            have successor == mid;
                                                            have aligned(successor, 8);
                                                            have child == rid;

                                                            mark transplant;
                                                            have ctx_node_is(up.model, tmp) == 1;
                                                            let { links: incoming, frame: outer_frame } = detach_erase_links(node, tmp, root, { before: up });
                                                            observe(erase_callbacks(augment));
                                                            mark incoming_link_state;
                                                            let { sibling_ptr: sibling_ptr, root_count: root_count, parent_count: parent_count, tag: parent_tag, above: above } = unfold(incoming);
                                                            have separate(memory(root[0..root_count]), memory(*augment)) by close();
                                                            have separate(memory(tmp[0..parent_count]), memory(*augment)) by close();
                                                            let incoming = fold(erase_change_links(node, tmp, root), {
                                                                model: at(incoming_link_state, incoming.model), sibling_ptr: sibling_ptr,
                                                                root_count: root_count, parent_count: parent_count, tag: parent_tag, above: above
                                                            });
                                                            let { updated: linked } = step(__rb_change_child, { links: incoming });
                                                            have linked.model == outer_frame.model;
                                                            have linked.sibling_ptr == outer_frame.sibling_ptr;
                                                            have linked.tag == outer_frame.tag;
                                                            have linked.above == outer_frame.above;
                                                            let { updated: context } = attach_erase_links(successor, tmp, root, { links: linked, frame: outer_frame });
                                                            have child->rb_right == at(transplant, child->rb_right);
                                                            have at(after_detaching_successor, parent->rb_left) == child2 by close();
                                                            have at(before_linking_successor, parent->rb_left) == at(after_detaching_successor, parent->rb_left) by close();
                                                            have separate(memory(successor->rb_right), memory(parent->rb_left)) by close();
                                                            have separate(region(37).footprint, memory(parent->rb_left)) by {
                                                                normalize() using { separate(memory(successor->rb_right), memory(parent->rb_left)); };
                                                            }
                                                            have at(after_linking_successor, parent->rb_left) == at(before_linking_successor, parent->rb_left) by {
                                                                preserve(memory(parent->rb_left), region(37));
                                                            }
                                                            have at(after_linking_successor, parent->rb_left) == child2 by close();
                                                            have at(before_reparent, parent->rb_left) == at(after_linking_successor, parent->rb_left) by close();
                                                            have separate(memory(child->__rb_parent_color), memory(parent->rb_left)) by close();
                                                            have separate(region(38).footprint, memory(parent->rb_left)) by {
                                                                normalize() using { separate(memory(child->__rb_parent_color), memory(parent->rb_left)); };
                                                            }
                                                            have at(after_child_reparent, parent->rb_left) == at(before_reparent, parent->rb_left) by {
                                                                preserve(memory(parent->rb_left), region(38));
                                                            }
                                                            have at(after_child_reparent, parent->rb_left) == child2 by close();
                                                            have at(before_copy, parent->rb_left) == at(after_child_reparent, parent->rb_left) by close();
                                                            have separate(region(39).footprint, memory(parent->rb_left)) by {
                                                                normalize() using { };
                                                            }
                                                            have at(before_propagate, parent->rb_left) == at(before_copy, parent->rb_left) by {
                                                                preserve(memory(parent->rb_left), region(39));
                                                            }
                                                            have at(before_propagate, parent->rb_left) == child2 by close();
                                                            have separate(region(40).footprint, memory(parent->rb_left)) by {
                                                                normalize() using { };
                                                            }
                                                            have at(before_reading_left_child, parent->rb_left) == at(before_propagate, parent->rb_left) by {
                                                                preserve(memory(parent->rb_left), region(40));
                                                            }
                                                            have at(before_reading_left_child, parent->rb_left) == child2 by close();
                                                            have separate(region(41).footprint, memory(parent->rb_left)) by {
                                                                normalize() using { };
                                                            }
                                                            have at(before_linking_left_child, parent->rb_left) == at(before_reading_left_child, parent->rb_left) by {
                                                                preserve(memory(parent->rb_left), region(41));
                                                            }
                                                            have at(before_linking_left_child, parent->rb_left) == child2 by close();
                                                            have separate(memory(successor->rb_left), memory(parent->rb_left)) by close();
                                                            have separate(region(42).footprint, memory(parent->rb_left)) by {
                                                                normalize() using { separate(memory(successor->rb_left), memory(parent->rb_left)); };
                                                            }
                                                            have at(after_linking_left_child, parent->rb_left) == at(before_linking_left_child, parent->rb_left) by {
                                                                preserve(memory(parent->rb_left), region(42));
                                                            }
                                                            have parent->rb_left == at(after_linking_left_child, parent->rb_left) by close();
                                                            have parent->rb_left == child2 by close();
                                                            have context.model == at(transplant, up.model) by close();
                                                            have context.model == old(up.model);
                                                            unfold(successor_color);
                                                            have (mid->__rb_parent_color & 1) == color_bit(mc) by close();
                                                            have (successor->__rb_parent_color & 1) == color_bit(mc) by {
                                                                rewrite(successor, mid); close();
                                                            }
                                                            have at(transplant, child->rb_right) == at(after_left_reparent, child->rb_right) by close();
                                                            have child->rb_right == at(erased_parent_initial, node->rb_right->rb_right) by close();
                                                            let retained_right = fold(erase_saved_right(child), { child: at(erased_parent_initial, node->rb_right->rb_right) });
                                                            observe(erase_callbacks(augment));
                                                            have separate(memory(parent->rb_left), memory(*augment)) by close();
                                                            have contains(memory(parent->rb_left), memory(((&parent->rb_left) as (uint8*))[0..8])) by {
                                                                normalize();
                                                            }
                                                            apply(separation::contains_refl(memory(*augment)));
                                                            apply(separation::separate_restrict(memory(parent->rb_left), memory(*augment),
                                                                memory(((&parent->rb_left) as (uint8*))[0..8]), memory(*augment)));
                                                            let retained_detached = fold(erase_saved_left(parent), { child: child2 });
                                                            have separate(memory((node as (uint64*))[0..3]), memory(*augment)) by close();
                                                            have contains(memory((node as (uint64*))[0..3]), memory((node as (uint8*))[0..8])) by {
                                                                normalize();
                                                            }
                                                            apply(separation::separate_restrict(memory((node as (uint64*))[0..3]), memory(*augment),
                                                                memory((node as (uint8*))[0..8]), memory(*augment)));
                                                            mark parent_link_changed;
                                                            // Join the replacement link and the successor fields needed
                                                            // by the shared descent-spine and outer-context rebuild.
                                                            match min_right.model ensuring {
                                                                owns moved_link: erase_left_at(parent);
                                                                owns transplanted_tag: erase_saved_parent(tmp, parent_model);
                                                                fact moved_link.model == rb_reparent(rb_recolor(mr, Color::Black), mp);
                                                            } {
                                                                RbTree::Empty => {
                                                                    have mr == RbTree::Empty by { rewrite(mr, min_right.model); close(); }
                                                                    have mc == Color::Red by {
                                                                        cases {
                                                                            not(mr == RbTree::Empty) => { contradiction(mr == RbTree::Empty); }
                                                                            mc == Color::Red => { close(); }
                                                                        }
                                                                    }
                                                                    unfold(min_right);
                                                                    have color_bit(mc) == 0 by { rewrite(mc, Color::Red); unfold(color_bit(Color::Red)); normalize(); }
                                                                    have (successor->__rb_parent_color & 1) == 0 by {
                                                                        rewrite((successor->__rb_parent_color & 1), color_bit(mc));
                                                                        rewrite(color_bit(mc), 0);
                                                                        normalize();
                                                                    }
                                                                    have child2 == 0;
                                                                    step_until(statement(4).statement(5).statement(15).entry);
                                                                    mark before_copying_tag;
                                                                    have ((pc & ~3) as (struct rb_node *)) == parent_model by close();
                                                                    step();
                                                                    have successor->__rb_parent_color == at(before_copying_tag, pc) by close();
                                                                    have ((successor->__rb_parent_color & ~3) as (struct rb_node *)) == parent_model by close();
                                                                    let transplanted_tag = fold(erase_saved_parent(successor, parent_model), {
                                                                        word: at(before_copying_tag, pc), color: color
                                                                    });
                                                                    step_until(statement(5).entry);
                                                                    let moved_child = fold(rb_at(0), { model: RbTree::Empty });
                                                                    have moved_child.model == rb_reparent(rb_recolor(mr, Color::Black), mp) by {
                                                                        rewrite(mr, RbTree::Empty);
                                                                        unfold(rb_recolor(RbTree::Empty, Color::Black));
                                                                        unfold(rb_reparent(RbTree::Empty, mp)); normalize();
                                                                    }
                                                                    unfold(retained_detached);
                                                                    have parent->rb_left == 0 by close();
                                                                    let moved_link = fold(erase_left_at(parent), { model: moved_child.model, tree: moved_child });
                                                                },
                                                                RbTree::Node(cid, cp, cc, cl, cr) => {
                                                                    have mr == RbTree::Node(cid, cp, cc, cl, cr) by { rewrite(mr, min_right.model); close(); }
                                                                    have rb_reparent(rb_recolor(mr, Color::Black), mp) == RbTree::Node(cid, mp, Color::Black, cl, cr) by {
                                                                        rewrite(mr, RbTree::Node(cid, cp, cc, cl, cr));
                                                                        unfold(rb_recolor(RbTree::Node(cid, cp, cc, cl, cr), Color::Black));
                                                                        unfold(rb_reparent(RbTree::Node(cid, cp, Color::Black, cl, cr), mp)); normalize();
                                                                    }
                                                                    let { left: child_left, right: child_right } = unfold(min_right);
                                                                    have child2 == cid;
                                                                    have parent == mp;
                                                                    have child_left.model == cl;
                                                                    have child_right.model == cr;
                                                                    step(); step();
                                                                    have child2->__rb_parent_color == (address(parent) | 1) by close();
                                                                    have child2->__rb_parent_color == (address(mp) | 1) by { rewrite(mp, parent); close(); }
                                                                    have aligned(mp, 8);
                                                                    have ((address(mp) | 1) & 1) == 1 by { close() using { aligned(mp, 8); }; }
                                                                    have (child2->__rb_parent_color & 1) == color_bit(Color::Black) by {
                                                                        unfold(color_bit(Color::Black));
                                                                    }
                                                                    have (address(mp) | 1) == address(mp) + ((address(mp) | 1) & 1) by {
                                                                        close() using { aligned(mp, 8); };
                                                                    }
                                                                    have child2->__rb_parent_color == address(mp) + (child2->__rb_parent_color & 1) by {
                                                                        rewrite(child2->__rb_parent_color, (address(mp) | 1)); close();
                                                                    }

                                                                    let moved_child = fold(rb_at(child2), { model: RbTree::Node(cid, mp, Color::Black, cl, cr), left: child_left, right: child_right });
                                                                    step_until(statement(4).statement(5).statement(15).entry);
                                                                    mark before_copying_tag;
                                                                    have ((pc & ~3) as (struct rb_node *)) == parent_model by close();
                                                                    step();
                                                                    have successor->__rb_parent_color == at(before_copying_tag, pc) by close();
                                                                    have ((successor->__rb_parent_color & ~3) as (struct rb_node *)) == parent_model by close();
                                                                    let transplanted_tag = fold(erase_saved_parent(successor, parent_model), {
                                                                        word: at(before_copying_tag, pc), color: color
                                                                    });
                                                                    step_until(statement(5).entry);
                                                                    unfold(retained_detached);
                                                                    have parent->rb_left == cid by close();
                                                                    have moved_child.model == rb_reparent(rb_recolor(mr, Color::Black), mp) by {
                                                                        rewrite(rb_reparent(rb_recolor(mr, Color::Black), mp), RbTree::Node(cid, mp, Color::Black, cl, cr)); normalize();
                                                                    }
                                                                    let moved_link = fold(erase_left_at(parent), { model: moved_child.model, tree: moved_child });
                                                                },
                                                            }
                                                            have separate(memory(child->__rb_parent_color), memory(parent->rb_left));
                                                            mark replacement_joined;
                                                            let { tree: moved_child } = unfold(moved_link);
                                                            have moved_child.model == rb_reparent(rb_recolor(mr, Color::Black), mp);
                                                            mark closing_spine;
                                                            let { c: path2 } = close_erase_spine_link(parent->rb_left, parent, child, { frame: link_frame });
                                                            have path2.model == at(closing_spine, link_frame.model) by close();
                                                            have path2.model == mu;
                                                            have rb_parent_consistent(plug(erase_context(path2.model), moved_child.model), child) == 1 by {
                                                                rewrite(path2.model, mu);
                                                                rewrite(moved_child.model, rb_reparent(rb_recolor(mr, Color::Black), mp));
                                                                rewrite(plug(erase_context(mu), rb_reparent(rb_recolor(mr, Color::Black), mp)), rb_remove_min_blackened(rl));
                                                                rewrite(child, rid); close();
                                                            }
                                                            mark rebuilding_spine;
                                                            let { whole: spine_left } = refold_erase_spine(parent->rb_left, child, { c: path2, t: moved_child });
                                                            have at(rebuilding_spine, path2.model) == mu by close();
                                                            have spine_left.model == plug(erase_context(at(rebuilding_spine, path2.model)), at(rebuilding_spine, moved_child.model)) by close();
                                                            have at(rebuilding_spine, moved_child.model) == rb_reparent(rb_recolor(mr, Color::Black), mp) by close();
                                                            let { tree: rebuilt_left } = unfold(spine_left);
                                                            apply(erase_parent_consistent_parent_is(rb_remove_min_blackened(rl), rid));
                                                            have child->rb_left == rid->rb_left;
                                                            unfold(retained_anchor_tag);
                                                            unfold(retained_right);
                                                            let moved_right = fold(rb_at(child), {
                                                                model: RbTree::Node(rid, mid, rc, rb_remove_min_blackened(rl), rr),
                                                                left: rebuilt_left, right: right_sibling
                                                            });
                                                            have rb_parent_is(RbTree::Node(lid, mid, lc, ll, lr), mid) == 1 by { unfold(rb_parent_is(RbTree::Node(lid, mid, lc, ll, lr), mid)); normalize(); }
                                                            have rb_parent_is(RbTree::Node(rid, mid, rc, rb_remove_min_blackened(rl), rr), mid) == 1 by { unfold(rb_parent_is(RbTree::Node(rid, mid, rc, rb_remove_min_blackened(rl), rr), mid)); normalize(); }
                                                            unfold(transplanted_left);
                                                            unfold(transplanted_right);
                                                            have tmp == mid by close();
                                                            have tmp->rb_left == lid by close();
                                                            have tmp->rb_right == child by close();
                                                            unfold(transplanted_tag);
                                                            have ((tmp->__rb_parent_color & ~3) as (struct rb_node *)) == parent_model by close();
                                                            let subtree = fold(rb_at(tmp), {
                                                                model: RbTree::Node(tmp, parent_model, color, RbTree::Node(lid, mid, lc, ll, lr),
                                                                    RbTree::Node(rid, mid, rc, rb_remove_min_blackened(rl), rr)),
                                                                left: moved_left, right: moved_right
                                                            });
                                                            have subtree.model == rb_successor_child_splice(mid, parent_model, color, left_model, right_model) by {
                                                                unfold(rb_successor_child_splice(mid, parent_model, color, left_model, right_model));
                                                                rewrite(left_model, RbTree::Node(lid, lp, lc, ll, lr));
                                                                rewrite(right_model, RbTree::Node(rid, rp, rc, rl, rr));
                                                                rewrite(rb_remove_min_blackened(RbTree::Node(rid, rp, rc, rl, rr)), RbTree::Node(rid, rp, rc, rb_remove_min_blackened(rl), rr));
                                                                unfold(rb_reparent(RbTree::Node(lid, lp, lc, ll, lr), mid));
                                                                unfold(rb_reparent(RbTree::Node(rid, rp, rc, rb_remove_min_blackened(rl), rr), mid));
                                                                rewrite(tmp, mid);
                                                                normalize();
                                                            }
                                                            have subtree.model == erase_child_deep_model(old(tree.model)) by {
                                                                rewrite(old(tree.model), RbTree::Node(identity, parent_model, color, left_model, right_model));
                                                                unfold(erase_child_deep_model(RbTree::Node(identity, parent_model, color, left_model, right_model)));
                                                                rewrite(erase_minimum_identity(rb_minimum(right_model)), mid); close();
                                                            }
                                                            have is_rb_root(plug(context.model, subtree.model)) == 1 by {
                                                                rewrite(context.model, old(up.model));
                                                                rewrite(subtree.model, rb_successor_child_splice(mid, parent_model, color, left_model, right_model)); close();
                                                            }
                                                            apply(plug_parent_consistent_transport(context.model, subtree.model, 0));
                                                            have rb_tree_parent_consistent(plug(context.model, subtree.model)) == 1 by {
                                                                unfold(rb_tree_parent_consistent(plug(context.model, subtree.model))); close();
                                                            }
                                                            have plug(context.model, subtree.model) == plug(old(up.model), erase_child_deep_model(old(tree.model))) by {
                                                                rewrite(context.model, old(up.model));
                                                                rewrite(subtree.model, erase_child_deep_model(old(tree.model))); normalize();
                                                            }
                                                            have rb_inorder(erase_child_deep_model(old(tree.model))) == list::append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model)))) by {
                                                                rewrite(erase_child_deep_model(old(tree.model)), subtree.model); close();
                                                            }
                                                            mark closing_root;
                                                            let { whole: deep_whole } = refold_to_root(mid, root, { c: context, t: subtree });
                                                            have deep_whole.model == plug(old(up.model), erase_child_deep_model(old(tree.model))) by {
                                                                rewrite(deep_whole.model, plug(at(closing_root, context.model),
                                                                    RbTree::Node(mid, parent_model, color, RbTree::Node(lid, mid, lc, ll, lr),
                                                                        RbTree::Node(rid, mid, rc, rb_remove_min_blackened(rl), rr))));
                                                                close();
                                                            }
                                                            have is_rb_root(deep_whole.model) == 1 by {
                                                                rewrite(deep_whole.model, plug(at(closing_root, context.model),
                                                                    RbTree::Node(mid, parent_model, color, RbTree::Node(lid, mid, lc, ll, lr),
                                                                        RbTree::Node(rid, mid, rc, rb_remove_min_blackened(rl), rr)))); close();
                                                            }
                                                            observe(erase_callbacks(augment));
                                                            step_until(function.exit);
                                                            apply(erase_deep_no_fixup(old(tree.model), old(up.model), mid, mc, mr));
                                                            apply(erase_outcome_deep(identity, parent_model, color, lid, lp, lc, ll, lr, rid, rp, rc, iid, ip, ic, il, ir, rr, old(up.model)));
                                                            have old(tree.model) == RbTree::Node(identity, parent_model, color, RbTree::Node(lid, lp, lc, ll, lr), RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr)) by {
                                                                rewrite(old(tree.model), RbTree::Node(identity, parent_model, color, left_model, right_model));
                                                                rewrite(left_model, RbTree::Node(lid, lp, lc, ll, lr));
                                                                rewrite(right_model, RbTree::Node(rid, rp, rc, rl, rr));
                                                                rewrite(rl, RbTree::Node(iid, ip, ic, il, ir)); normalize();
                                                            }
                                                            have rb_minimum(RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr)) == RbMinimum::Found(mid, mc, mr) by {
                                                                rewrite(RbTree::Node(iid, ip, ic, il, ir), rl);
                                                                rewrite(RbTree::Node(rid, rp, rc, rl, rr), right_model); close();
                                                            }
                                                            have erase_outcome(old(tree.model), old(up.model)) == EraseOutcome::Balanced(plug(old(up.model), erase_child_deep_model(old(tree.model)))) by {
                                                                rewrite(old(tree.model), RbTree::Node(identity, parent_model, color, RbTree::Node(lid, lp, lc, ll, lr), RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr)));
                                                                rewrite(erase_outcome(RbTree::Node(identity, parent_model, color, RbTree::Node(lid, lp, lc, ll, lr), RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr)), old(up.model)), erase_deep_outcome(RbTree::Node(identity, parent_model, color, RbTree::Node(lid, lp, lc, ll, lr), RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr)), old(up.model), rb_minimum(RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr))));
                                                                rewrite(rb_minimum(RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr)), RbMinimum::Found(mid, mc, mr));
                                                                rewrite(RbTree::Node(identity, parent_model, color, RbTree::Node(lid, lp, lc, ll, lr), RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr)), old(tree.model)); close();
                                                            }
                                                            have erase_splice(old(tree.model)) == erase_child_deep_model(old(tree.model)) by {
                                                                rewrite(old(tree.model), RbTree::Node(identity, parent_model, color, RbTree::Node(lid, lp, lc, ll, lr), RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr)));
                                                                rewrite(erase_splice(RbTree::Node(identity, parent_model, color, RbTree::Node(lid, lp, lc, ll, lr), RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr))), erase_deep_splice(RbTree::Node(identity, parent_model, color, RbTree::Node(lid, lp, lc, ll, lr), RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr)), rb_minimum(RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr))));
                                                                rewrite(rb_minimum(RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr)), RbMinimum::Found(mid, mc, mr));
                                                                rewrite(RbTree::Node(identity, parent_model, color, RbTree::Node(lid, lp, lc, ll, lr), RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr)), old(tree.model)); close();
                                                            }
                                                            have rb_inorder(erase_splice(old(tree.model))) == list::append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model)))) by {
                                                                rewrite(erase_splice(old(tree.model)), erase_child_deep_model(old(tree.model))); close();
                                                            }
                                                            have rb_tree_parent_consistent(plug(old(up.model), erase_child_deep_model(old(tree.model)))) == 1 by {
                                                            unfold(rb_tree_parent_consistent(plug(old(up.model), erase_child_deep_model(old(tree.model))))); rewrite(plug(old(up.model), erase_child_deep_model(old(tree.model))), deep_whole.model); close();
                                                            }
                                                            have is_rb_root(plug(old(up.model), erase_child_deep_model(old(tree.model)))) == 1 by { rewrite(plug(old(up.model), erase_child_deep_model(old(tree.model))), deep_whole.model); close(); }
                                                            let out = fold(erase_out(root, result), { model: EraseOutcome::Balanced(plug(old(up.model), erase_child_deep_model(old(tree.model)))), whole: deep_whole });
                                                            have erase_out_rb(out.model) == 1 by {
                                                            rewrite(out.model, EraseOutcome::Balanced(plug(old(up.model), erase_child_deep_model(old(tree.model)))));
                                                            unfold(erase_out_rb(EraseOutcome::Balanced(plug(old(up.model), erase_child_deep_model(old(tree.model)))))); close();
                                                            }
                                                            have erase_out_tree(out.model) == plug(old(up.model), erase_child_deep_model(old(tree.model))) by {
                                                            rewrite(out.model, EraseOutcome::Balanced(plug(old(up.model), erase_child_deep_model(old(tree.model)))));
                                                            unfold(erase_out_tree(EraseOutcome::Balanced(plug(old(up.model), erase_child_deep_model(old(tree.model)))))); normalize();
                                                            }
                                                            have rb_tree_parent_consistent(erase_out_tree(out.model)) == 1 by {
                                                            rewrite(erase_out_tree(out.model), plug(old(up.model), erase_child_deep_model(old(tree.model)))); close();
                                                            }
                                                            have out.model == erase_outcome(old(tree.model), old(up.model)) by {
                                                            rewrite(erase_outcome(old(tree.model), old(up.model)), EraseOutcome::Balanced(plug(old(up.model), erase_child_deep_model(old(tree.model))))); rewrite(out.model, EraseOutcome::Balanced(plug(old(up.model), erase_child_deep_model(old(tree.model))))); normalize();
                                                            }
                                                            have erase_out_tree(out.model) == plug(old(up.model), erase_splice(old(tree.model))) by {
                                                            rewrite(erase_splice(old(tree.model)), erase_child_deep_model(old(tree.model))); close();
                                                            }
                                                            close();
                                                        },
                                                    }
                                                },
                                            }
                                        },
                                    }
                                },
                            }
                        },
                    }
                },
            }
        }
    } else {
    match tree.model {
        RbTree::Empty => { contradiction(tree.model == RbTree::Empty); },
        RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right) => {
            match erased_left {
                RbTree::Empty => {
                    match erased_right {
                        RbTree::Empty => {
                            // Leaf: unlink it. A black leaf below the root leaves a deficit at its parent.
                            have rb_left(old(tree.model)) == RbTree::Empty;
                            have rb_right(old(tree.model)) == RbTree::Empty;
                            have erase_outcome(old(tree.model), old(up.model)) == erase_leaf_outcome(erased_color, old(up.model));
                            have erase_splice(old(tree.model)) == RbTree::Empty;
                            have rb_inorder(erase_splice(old(tree.model))) == list::append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model)))) by {
                                rewrite(erase_splice(old(tree.model)), RbTree::Empty);
                                rewrite(rb_left(old(tree.model)), RbTree::Empty); rewrite(rb_right(old(tree.model)), RbTree::Empty);
                                unfold(rb_inorder(RbTree::Empty));
                                unfold(list::append(List<struct rb_node*>::Nil, List<struct rb_node*>::Nil)); normalize();
                            }
                            apply(rb_parent_consistent_empty(erased_parent));
                            apply(ctx_consistent_swap(up.model, erased, erased_parent, erased_color, erased_left, erased_right, RbTree::Empty, 0));
                            let { left: l, right: r } = unfold(tree);
                            unfold(l); unfold(r);
                            have rb_color(old(tree.model)) == erased_color by {
                                rewrite(old(tree.model), RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right));
                                unfold(rb_color(RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right))); normalize();
                            }
                            apply(erase_context_parent(up.model, erased, erased_parent, erased_color, erased_left, erased_right));
                            apply(plug_parent_consistent_transport(old(up.model), RbTree::Empty, 0));
                            have rb_tree_parent_consistent(plug(old(up.model), RbTree::Empty)) == 1 by {
                                unfold(rb_tree_parent_consistent(plug(old(up.model), RbTree::Empty))); close();
                            }
                            match erased_color {
                                Color::Black => {
                                    have black_height(old(tree.model)) == Nat::Succ(Nat::Zero) by {
                                        rewrite(old(tree.model), RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right));
                                        rewrite(erased_color, Color::Black); rewrite(erased_left, RbTree::Empty);
                                        unfold(black_height(RbTree::Node(erased, erased_parent, Color::Black, RbTree::Empty, erased_right)));
                                        unfold(black_height(RbTree::Empty)); normalize();
                                    }
                                    have ctx_rb(old(up.model), Nat::Succ(Nat::Zero), Color::Black) == 1 by {
                                        rewrite(Nat::Succ(Nat::Zero), black_height(old(tree.model)));
                                        rewrite(Color::Black, erased_color);
                                        rewrite(erased_color, rb_color(old(tree.model))); close();
                                    }
                                    have (node->__rb_parent_color & 1) == 1 by {
                                        rewrite((node->__rb_parent_color & 1), color_bit(erased_color));
                                        rewrite(erased_color, Color::Black); unfold(color_bit(Color::Black)); normalize();
                                    }
                                    step_until(region(10).entry);
                                    have parent == erased_parent;
                                    have ctx_node_is(up.model, parent) == 1;
                                    let { links: incoming, frame: outer_frame } = detach_erase_links(node, parent, root, { before: up });
                                    observe(erase_callbacks(augment));
                                    mark incoming_link_state;
                                    let { sibling_ptr: sibling_ptr, root_count: root_count, parent_count: parent_count, tag: parent_tag, above: above } = unfold(incoming);
                                    have separate(memory(root[0..root_count]), memory(*augment)) by close();
                                    have separate(memory(parent[0..parent_count]), memory(*augment)) by close();
                                    let incoming = fold(erase_change_links(node, parent, root), {
                                        model: at(incoming_link_state, incoming.model), sibling_ptr: sibling_ptr,
                                        root_count: root_count, parent_count: parent_count, tag: parent_tag, above: above
                                    });
                                    let { updated: linked } = step(__rb_change_child, { links: incoming });
                                    have linked.model == outer_frame.model;
                                    have linked.sibling_ptr == outer_frame.sibling_ptr;
                                    have linked.tag == outer_frame.tag;
                                    have linked.above == outer_frame.above;
                                    let { updated: remaining } = attach_erase_links(child, parent, root, { links: linked, frame: outer_frame });
                                    have remaining.model == old(up.model);
                                    match remaining.model {
                                        Context::Top => {
                                            have ctx_node_is(Context::Top, erased_parent) == 1 by {
                                                rewrite(Context::Top, remaining.model); rewrite(remaining.model, old(up.model)); close();
                                            }
                                            have erased_parent == 0;
                                            have old(up.model) == Context::Top by { rewrite(old(up.model), remaining.model); close(); }
                                            have is_rb_root(RbTree::Empty) == 1 by {
                                                unfold(is_rb_root(RbTree::Empty)); unfold(is_rb(RbTree::Empty)); unfold(rb_root_black(RbTree::Empty)); normalize();
                                            }
                                            have plug(old(up.model), RbTree::Empty) == RbTree::Empty by {
                                                rewrite(old(up.model), Context::Top); unfold(plug(Context::Top, RbTree::Empty)); normalize();
                                            }
                                            have rb_tree_parent_consistent(RbTree::Empty) == 1 by {
                                                rewrite(RbTree::Empty, plug(old(up.model), RbTree::Empty)); close();
                                            }
                                            have erase_leaf_outcome(erased_color, old(up.model)) == EraseOutcome::Balanced(RbTree::Empty) by {
                                                rewrite(erased_color, Color::Black); rewrite(old(up.model), Context::Top);
                                                unfold(erase_leaf_outcome(Color::Black, Context::Top)); normalize();
                                            }
                                            unfold(remaining);
                                            with(erase_callbacks(augment)) { step_until(function.exit); }
                                            let hole = fold(rb_at(0), { model: RbTree::Empty });
                                            let whole = fold(rb_root_at(root), { model: RbTree::Empty, tree: hole });
                                            have result == 0;
                                            let out = fold(erase_out(root, result), { model: EraseOutcome::Balanced(RbTree::Empty), whole: whole });
                                            have erase_out_rb(out.model) == 1 by {
                                                rewrite(out.model, EraseOutcome::Balanced(RbTree::Empty));
                                                unfold(erase_out_rb(EraseOutcome::Balanced(RbTree::Empty))); close();
                                            }
                                            have erase_out_tree(out.model) == RbTree::Empty by {
                                                rewrite(out.model, EraseOutcome::Balanced(RbTree::Empty));
                                                unfold(erase_out_tree(EraseOutcome::Balanced(RbTree::Empty))); normalize();
                                            }
                                            have out.model == erase_outcome(old(tree.model), old(up.model)) by {
                                                rewrite(out.model, EraseOutcome::Balanced(RbTree::Empty));
                                                rewrite(erase_outcome(old(tree.model), old(up.model)), erase_leaf_outcome(erased_color, old(up.model)));
                                                rewrite(erase_leaf_outcome(erased_color, old(up.model)), EraseOutcome::Balanced(RbTree::Empty));
                                                normalize();
                                            }
                                            have rb_tree_parent_consistent(erase_out_tree(out.model)) == 1 by {
                                                rewrite(out.model, EraseOutcome::Balanced(RbTree::Empty));
                                                unfold(erase_out_tree(EraseOutcome::Balanced(RbTree::Empty)));
                                                close();
                                            }
                                            have erase_out_tree(out.model) == plug(old(up.model), erase_splice(old(tree.model))) by {
                                                rewrite(out.model, EraseOutcome::Balanced(RbTree::Empty));
                                                unfold(erase_out_tree(EraseOutcome::Balanced(RbTree::Empty)));
                                                rewrite(erase_splice(old(tree.model)), RbTree::Empty);
                                                rewrite(plug(old(up.model), RbTree::Empty), RbTree::Empty);
                                                normalize();
                                            }
                                            close();
                                        },
                                        Context::Left(pid, gp, pc_model, sibling_model, above_model) => {
                                            have Context::Left(pid, gp, pc_model, sibling_model, above_model) == old(up.model) by {
                                                rewrite(Context::Left(pid, gp, pc_model, sibling_model, above_model), remaining.model); close();
                                            }
                                            have ctx_node_is(Context::Left(pid, gp, pc_model, sibling_model, above_model), erased_parent) == 1 by {
                                                rewrite(Context::Left(pid, gp, pc_model, sibling_model, above_model), old(up.model)); close();
                                            }
                                            have erased_parent == pid;
                                            have erase_leaf_outcome(erased_color, old(up.model)) == EraseOutcome::Deficit(old(up.model)) by {
                                                rewrite(erased_color, Color::Black);
                                                rewrite(old(up.model), Context::Left(pid, gp, pc_model, sibling_model, above_model));
                                                unfold(erase_leaf_outcome(Color::Black, Context::Left(pid, gp, pc_model, sibling_model, above_model))); normalize();
                                            }
                                            let { sibling: sibling, up: above } = unfold(remaining);
                                            have erased_parent != 0;
                                            let remaining = fold(ctx_at(0, root), { model: Context::Left(pid, gp, pc_model, sibling_model, above_model), up: above, sibling: sibling });
                                            have remaining.model == old(up.model) by { rewrite(remaining.model, Context::Left(pid, gp, pc_model, sibling_model, above_model)); close(); }
                                            have remaining.model != Context::Top by { rewrite(remaining.model, Context::Left(pid, gp, pc_model, sibling_model, above_model)); normalize(); }
                                            with(erase_callbacks(augment)) { step_until(function.exit); }
                                            have result != 0;
                                            have ctx_node_is(old(up.model), result) == 1 by { rewrite(result, erased_parent); close(); }
                                            have old(up.model) != Context::Top by { rewrite(old(up.model), remaining.model); close(); }
                                            let out = fold(erase_out(root, result), { model: EraseOutcome::Deficit(old(up.model)), deficit: remaining });
                                            have erase_out_rb(out.model) == 1 by {
                                                rewrite(out.model, EraseOutcome::Deficit(old(up.model)));
                                                unfold(erase_out_rb(EraseOutcome::Deficit(old(up.model)))); close();
                                            }
                                            have erase_out_tree(out.model) == plug(old(up.model), RbTree::Empty) by {
                                                rewrite(out.model, EraseOutcome::Deficit(old(up.model)));
                                                unfold(erase_out_tree(EraseOutcome::Deficit(old(up.model)))); normalize();
                                            }
                                            have out.model == erase_outcome(old(tree.model), old(up.model)) by {
                                                rewrite(out.model, EraseOutcome::Deficit(old(up.model)));
                                                rewrite(erase_outcome(old(tree.model), old(up.model)), erase_leaf_outcome(erased_color, old(up.model)));
                                                rewrite(erase_leaf_outcome(erased_color, old(up.model)), EraseOutcome::Deficit(old(up.model)));
                                                normalize();
                                            }
                                            have rb_tree_parent_consistent(erase_out_tree(out.model)) == 1 by {
                                                rewrite(out.model, EraseOutcome::Deficit(old(up.model)));
                                                unfold(erase_out_tree(EraseOutcome::Deficit(old(up.model))));
                                                close();
                                            }
                                            have erase_out_tree(out.model) == plug(old(up.model), erase_splice(old(tree.model))) by {
                                                rewrite(out.model, EraseOutcome::Deficit(old(up.model)));
                                                unfold(erase_out_tree(EraseOutcome::Deficit(old(up.model))));
                                                rewrite(erase_splice(old(tree.model)), RbTree::Empty);
                                                normalize();
                                            }
                                            close();
                                        },
                                        Context::Right(pid, gp, pc_model, sibling_model, above_model) => {
                                            have Context::Right(pid, gp, pc_model, sibling_model, above_model) == old(up.model) by {
                                                rewrite(Context::Right(pid, gp, pc_model, sibling_model, above_model), remaining.model); close();
                                            }
                                            have ctx_node_is(Context::Right(pid, gp, pc_model, sibling_model, above_model), erased_parent) == 1 by {
                                                rewrite(Context::Right(pid, gp, pc_model, sibling_model, above_model), old(up.model)); close();
                                            }
                                            have erased_parent == pid;
                                            have erase_leaf_outcome(erased_color, old(up.model)) == EraseOutcome::Deficit(old(up.model)) by {
                                                rewrite(erased_color, Color::Black);
                                                rewrite(old(up.model), Context::Right(pid, gp, pc_model, sibling_model, above_model));
                                                unfold(erase_leaf_outcome(Color::Black, Context::Right(pid, gp, pc_model, sibling_model, above_model))); normalize();
                                            }
                                            let { sibling: sibling, up: above } = unfold(remaining);
                                            let remaining = fold(ctx_at(0, root), { model: Context::Right(pid, gp, pc_model, sibling_model, above_model), up: above, sibling: sibling });
                                            have remaining.model == old(up.model) by { rewrite(remaining.model, Context::Right(pid, gp, pc_model, sibling_model, above_model)); close(); }
                                            have remaining.model != Context::Top by { rewrite(remaining.model, Context::Right(pid, gp, pc_model, sibling_model, above_model)); normalize(); }
                                            with(erase_callbacks(augment)) { step_until(function.exit); }
                                            have ctx_node_is(old(up.model), result) == 1 by { rewrite(result, erased_parent); close(); }
                                            have old(up.model) != Context::Top by { rewrite(old(up.model), remaining.model); close(); }
                                            let out = fold(erase_out(root, result), { model: EraseOutcome::Deficit(old(up.model)), deficit: remaining });
                                            have erase_out_rb(out.model) == 1 by {
                                                rewrite(out.model, EraseOutcome::Deficit(old(up.model)));
                                                unfold(erase_out_rb(EraseOutcome::Deficit(old(up.model)))); close();
                                            }
                                            have erase_out_tree(out.model) == plug(old(up.model), RbTree::Empty) by {
                                                rewrite(out.model, EraseOutcome::Deficit(old(up.model)));
                                                unfold(erase_out_tree(EraseOutcome::Deficit(old(up.model)))); normalize();
                                            }
                                            have out.model == erase_outcome(old(tree.model), old(up.model)) by {
                                                rewrite(out.model, EraseOutcome::Deficit(old(up.model)));
                                                rewrite(erase_outcome(old(tree.model), old(up.model)), erase_leaf_outcome(erased_color, old(up.model)));
                                                rewrite(erase_leaf_outcome(erased_color, old(up.model)), EraseOutcome::Deficit(old(up.model)));
                                                normalize();
                                            }
                                            have rb_tree_parent_consistent(erase_out_tree(out.model)) == 1 by {
                                                rewrite(out.model, EraseOutcome::Deficit(old(up.model)));
                                                unfold(erase_out_tree(EraseOutcome::Deficit(old(up.model))));
                                                close();
                                            }
                                            have erase_out_tree(out.model) == plug(old(up.model), erase_splice(old(tree.model))) by {
                                                rewrite(out.model, EraseOutcome::Deficit(old(up.model)));
                                                unfold(erase_out_tree(EraseOutcome::Deficit(old(up.model))));
                                                rewrite(erase_splice(old(tree.model)), RbTree::Empty);
                                                normalize();
                                            }
                                            close();
                                        },
                                    }
                                },
                                Color::Red => {
                                    have black_height(old(tree.model)) == Nat::Zero by {
                                        rewrite(old(tree.model), RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right));
                                        rewrite(erased_color, Color::Red); rewrite(erased_left, RbTree::Empty);
                                        unfold(black_height(RbTree::Node(erased, erased_parent, Color::Red, RbTree::Empty, erased_right)));
                                        unfold(black_height(RbTree::Empty)); normalize();
                                    }
                                    have ctx_rb(old(up.model), Nat::Zero, Color::Red) == 1 by {
                                        rewrite(Nat::Zero, black_height(old(tree.model)));
                                        rewrite(Color::Red, erased_color);
                                        rewrite(erased_color, rb_color(old(tree.model))); close();
                                    }
                                    have erase_leaf_outcome(erased_color, old(up.model)) == EraseOutcome::Balanced(plug(old(up.model), RbTree::Empty)) by {
                                        rewrite(erased_color, Color::Red);
                                        unfold(erase_leaf_outcome(Color::Red, old(up.model))); normalize();
                                    }
                                    have (node->__rb_parent_color & 1) == 0 by {
                                        rewrite((node->__rb_parent_color & 1), color_bit(erased_color));
                                        rewrite(erased_color, Color::Red); unfold(color_bit(Color::Red)); normalize();
                                    }
                                    step_until(region(10).entry);
                                    have ctx_node_is(up.model, parent) == 1;
                                    let { links: incoming, frame: outer_frame } = detach_erase_links(node, parent, root, { before: up });
                                    observe(erase_callbacks(augment));
                                    mark incoming_link_state;
                                    let { sibling_ptr: sibling_ptr, root_count: root_count, parent_count: parent_count, tag: parent_tag, above: above } = unfold(incoming);
                                    have separate(memory(root[0..root_count]), memory(*augment)) by close();
                                    have separate(memory(parent[0..parent_count]), memory(*augment)) by close();
                                    let incoming = fold(erase_change_links(node, parent, root), {
                                        model: at(incoming_link_state, incoming.model), sibling_ptr: sibling_ptr,
                                        root_count: root_count, parent_count: parent_count, tag: parent_tag, above: above
                                    });
                                    let { updated: linked } = step(__rb_change_child, { links: incoming });
                                    have linked.model == outer_frame.model;
                                    have linked.sibling_ptr == outer_frame.sibling_ptr;
                                    have linked.tag == outer_frame.tag;
                                    have linked.above == outer_frame.above;
                                    let { updated: remaining } = attach_erase_links(child, parent, root, { links: linked, frame: outer_frame });
                                    apply(ctx_rb_black_focus(old(up.model), Nat::Zero, Color::Red));
                                    have ctx_rb(old(up.model), black_height(RbTree::Empty), rb_color(RbTree::Empty)) == 1 by {
                                        unfold(black_height(RbTree::Empty)); unfold(rb_color(RbTree::Empty)); close();
                                    }
                                    apply(plug_rb_from_ctx_rb(old(up.model), RbTree::Empty));
                                    let hole = fold(rb_at(0), { model: RbTree::Empty });
                                    have rb_tree_parent_consistent(plug(remaining.model, hole.model)) == 1 by {
                                        rewrite(remaining.model, old(up.model)); rewrite(hole.model, RbTree::Empty); close();
                                    }
                                    have plug(remaining.model, hole.model) == plug(old(up.model), RbTree::Empty) by {
                                        rewrite(remaining.model, old(up.model)); rewrite(hole.model, RbTree::Empty); normalize();
                                    }
                                    mark balanced;
                                    let { whole: whole } = refold_to_root(0, root, { c: remaining, t: hole });
                                    have whole.model == plug(old(up.model), RbTree::Empty) by {
                                        rewrite(whole.model, plug(at(balanced, remaining.model), RbTree::Empty));
                                        rewrite(at(balanced, remaining.model), old(up.model)); normalize();
                                    }
                                    with(erase_callbacks(augment)) { step_until(function.exit); }
                                    let out = fold(erase_out(root, result), { model: EraseOutcome::Balanced(plug(old(up.model), RbTree::Empty)), whole: whole });
                                    have erase_out_rb(out.model) == 1 by {
                                        rewrite(out.model, EraseOutcome::Balanced(plug(old(up.model), RbTree::Empty)));
                                        unfold(erase_out_rb(EraseOutcome::Balanced(plug(old(up.model), RbTree::Empty)))); close();
                                    }
                                    have erase_out_tree(out.model) == plug(old(up.model), RbTree::Empty) by {
                                        rewrite(out.model, EraseOutcome::Balanced(plug(old(up.model), RbTree::Empty)));
                                        unfold(erase_out_tree(EraseOutcome::Balanced(plug(old(up.model), RbTree::Empty)))); normalize();
                                    }
                                    have out.model == erase_outcome(old(tree.model), old(up.model)) by {
                                        rewrite(out.model, EraseOutcome::Balanced(plug(old(up.model), RbTree::Empty)));
                                        rewrite(erase_outcome(old(tree.model), old(up.model)), erase_leaf_outcome(erased_color, old(up.model)));
                                        rewrite(erase_leaf_outcome(erased_color, old(up.model)), EraseOutcome::Balanced(plug(old(up.model), RbTree::Empty)));
                                        normalize();
                                    }
                                    have rb_tree_parent_consistent(erase_out_tree(out.model)) == 1 by {
                                        rewrite(out.model, EraseOutcome::Balanced(plug(old(up.model), RbTree::Empty)));
                                        unfold(erase_out_tree(EraseOutcome::Balanced(plug(old(up.model), RbTree::Empty))));
                                        close();
                                    }
                                    have erase_out_tree(out.model) == plug(old(up.model), erase_splice(old(tree.model))) by {
                                        rewrite(out.model, EraseOutcome::Balanced(plug(old(up.model), RbTree::Empty)));
                                        unfold(erase_out_tree(EraseOutcome::Balanced(plug(old(up.model), RbTree::Empty))));
                                        rewrite(erase_splice(old(tree.model)), RbTree::Empty);
                                        normalize();
                                    }
                                    close();
                                },
                            }
                        },
                        RbTree::Node(er_id, er_parent, er_color, er_left, er_right) => {
                            // Only a right child: the black erased node's red child takes its parent
                            // word and becomes black, so no repair is needed.
                            have rb_left(old(tree.model)) == RbTree::Empty;
                            have rb_right(old(tree.model)) == erased_right;
                            have erase_outcome(old(tree.model), old(up.model)) == EraseOutcome::Balanced(plug(old(up.model), rb_erase_one_child_model(old(tree.model))));
                            have erase_splice(old(tree.model)) == rb_erase_one_child_model(old(tree.model));
                            have erased_right != RbTree::Empty;
                            have ctx_rb(up.model, black_height(RbTree::Node(erased, erased_parent, erased_color, RbTree::Empty, erased_right)),
                                rb_color(RbTree::Node(erased, erased_parent, erased_color, RbTree::Empty, erased_right))) == 1 by {
                                rewrite(RbTree::Empty, erased_left);
                                rewrite(RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right), tree.model); close();
                            }
                            apply(rb_erase_only_right_child(erased, erased_parent, erased_color, erased_right, up.model));
                            apply(ctx_consistent_node_children(up.model, erased, erased_parent, erased_color, erased_left, erased_right, 0));
                            apply(rb_erase_child_keeps_parents(up.model, erased, erased_parent, erased_color, erased_left, erased_right, erased_right));
                            apply(erase_context_parent(up.model, erased, erased_parent, erased_color, erased_left, erased_right));
                            apply(plug_parent_consistent_transport(up.model, rb_reparent(rb_recolor(erased_right, Color::Black), erased_parent), 0));
                            have rb_tree_parent_consistent(plug(old(up.model), rb_reparent(rb_recolor(erased_right, Color::Black), erased_parent))) == 1 by {
                                unfold(rb_tree_parent_consistent(plug(old(up.model), rb_reparent(rb_recolor(erased_right, Color::Black), erased_parent))));
                            }
                            have rb_reparent(rb_recolor(erased_right, Color::Black), erased_parent)
                                == RbTree::Node(er_id, erased_parent, Color::Black, er_left, er_right) by {
                                rewrite(erased_right, RbTree::Node(er_id, er_parent, er_color, er_left, er_right));
                                unfold(rb_recolor(RbTree::Node(er_id, er_parent, er_color, er_left, er_right), Color::Black));
                                unfold(rb_reparent(RbTree::Node(er_id, er_parent, Color::Black, er_left, er_right), erased_parent)); normalize();
                            }
                            have rb_erase_one_child_model(old(tree.model)) == rb_reparent(rb_recolor(erased_right, Color::Black), erased_parent) by {
                                rewrite(old(tree.model), RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right));
                                unfold(rb_erase_one_child_model(RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right)));
                                rewrite(erased_left, RbTree::Empty);
                                unfold(rb_erase_root_child(RbTree::Node(erased, erased_parent, erased_color, RbTree::Empty, erased_right))); normalize();
                            }
                            have rb_inorder(erase_splice(old(tree.model))) == list::append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model)))) by {
                                rewrite(erase_splice(old(tree.model)), rb_erase_one_child_model(old(tree.model)));
                                rewrite(rb_erase_one_child_model(old(tree.model)), rb_reparent(rb_recolor(erased_right, Color::Black), erased_parent));
                                rewrite(rb_inorder(rb_reparent(rb_recolor(erased_right, Color::Black), erased_parent)), rb_inorder(erased_right));
                                rewrite(rb_left(old(tree.model)), RbTree::Empty); rewrite(rb_right(old(tree.model)), erased_right);
                                unfold(rb_inorder(RbTree::Empty));
                                unfold(list::append(List<struct rb_node*>::Nil, rb_inorder(erased_right))); normalize();
                            }
                            let { left: l, right: r } = unfold(tree);
                            unfold(l);
                            have (node->__rb_parent_color & 1) == 1 by {
                                rewrite((node->__rb_parent_color & 1), color_bit(erased_color));
                                rewrite(erased_color, Color::Black); unfold(color_bit(Color::Black)); normalize();
                            }
                            have (old(node->__rb_parent_color) & 1) == 1 by { rewrite(old(node->__rb_parent_color), node->__rb_parent_color); close(); }
                            with(erase_callbacks(augment)) {
                                step_until(statement(4).statement(2).entry);
                                have ctx_node_is(up.model, parent) == 1;
                                let { links: incoming, frame: outer_frame } = detach_erase_links(node, parent, root, { before: up });
                                observe(erase_callbacks(augment));
                                mark incoming_link_state;
                                let { sibling_ptr: sibling_ptr, root_count: root_count, parent_count: parent_count, tag: parent_tag, above: above } = unfold(incoming);
                                have separate(memory(root[0..root_count]), memory(*augment)) by close();
                                have separate(memory(parent[0..parent_count]), memory(*augment)) by close();
                                let incoming = fold(erase_change_links(node, parent, root), {
                                    model: at(incoming_link_state, incoming.model), sibling_ptr: sibling_ptr,
                                    root_count: root_count, parent_count: parent_count, tag: parent_tag, above: above
                                });
                                let { updated: linked } = step(__rb_change_child, { links: incoming });
                                have linked.model == outer_frame.model;
                                have linked.sibling_ptr == outer_frame.sibling_ptr;
                                have linked.tag == outer_frame.tag;
                                have linked.above == outer_frame.above;
                                let { updated: remaining } = attach_erase_links(child, parent, root, { links: linked, frame: outer_frame });
                                let { left: child_left, right: child_right } = unfold(r);
                                step();
                                mark before_child_tag;
                                have ErasePropagate(augment->propagate) by close();
                                step();
                                have separate(memory(child->__rb_parent_color), memory(*augment)) by close();
                                apply(click::separation::contains_refl(memory(child->__rb_parent_color)));
                                have contains(memory(*augment), memory(augment->propagate)) by { normalize() using { }; }
                                apply(click::separation::separate_restrict(memory(child->__rb_parent_color), memory(*augment), memory(child->__rb_parent_color), memory(augment->propagate)));
                                have separate(statement(4).statement(3).statement(0).footprint, memory(augment->propagate)) by {
                                    normalize() using { separate(memory(child->__rb_parent_color), memory(augment->propagate)); };
                                }
                                have augment->propagate == at(before_child_tag, augment->propagate) by {
                                    preserve(memory(augment->propagate), statement(4).statement(3).statement(0));
                                }
                                have ErasePropagate(at(before_child_tag, augment->propagate)) by close();
                                have ErasePropagate(augment->propagate) by close();
                                have er_id->__rb_parent_color == pc;
                                have pc == old(node->__rb_parent_color);
                                have (pc & 1) == color_bit(Color::Black) by {
                                    rewrite(pc, old(node->__rb_parent_color)); unfold(color_bit(Color::Black)); close();
                                }
                                let replacement = fold(rb_at(er_id), {
                                    model: RbTree::Node(er_id, erased_parent, Color::Black, er_left, er_right),
                                    left: child_left, right: child_right
                                });
                                have rb_tree_parent_consistent(plug(remaining.model, replacement.model)) == 1 by {
                                    rewrite(remaining.model, old(up.model));
                                    rewrite(replacement.model, rb_reparent(rb_recolor(erased_right, Color::Black), erased_parent));
                                    unfold(rb_tree_parent_consistent(plug(old(up.model), rb_reparent(rb_recolor(erased_right, Color::Black), erased_parent))));
                                    close();
                                }
                                mark balanced;
                                let { whole: whole } = refold_to_root(er_id, root, { c: remaining, t: replacement });
                                have whole.model == plug(old(up.model), rb_erase_one_child_model(old(tree.model))) by {
                                    rewrite(whole.model, plug(at(balanced, remaining.model), RbTree::Node(er_id, erased_parent, Color::Black, er_left, er_right)));
                                    rewrite(at(balanced, remaining.model), old(up.model));
                                    rewrite(rb_erase_one_child_model(old(tree.model)), rb_reparent(rb_recolor(erased_right, Color::Black), erased_parent));
                                    rewrite(rb_reparent(rb_recolor(erased_right, Color::Black), erased_parent), RbTree::Node(er_id, erased_parent, Color::Black, er_left, er_right));
                                    normalize();
                                }
                                step_until(statement(5).entry);
                                have ErasePropagate(augment->propagate) by close();
                                step(ErasePropagate);
                                step();
                                let out = fold(erase_out(root, result), { model: EraseOutcome::Balanced(plug(old(up.model), rb_erase_one_child_model(old(tree.model)))), whole: whole });
                                have erase_out_rb(out.model) == 1 by {
                                    rewrite(out.model, EraseOutcome::Balanced(plug(old(up.model), rb_erase_one_child_model(old(tree.model)))));
                                    unfold(erase_out_rb(EraseOutcome::Balanced(plug(old(up.model), rb_erase_one_child_model(old(tree.model))))));
                                    rewrite(rb_erase_one_child_model(old(tree.model)), rb_reparent(rb_recolor(erased_right, Color::Black), erased_parent));
                                    close();
                                }
                                have erase_out_tree(out.model) == plug(old(up.model), rb_erase_one_child_model(old(tree.model))) by {
                                    rewrite(out.model, EraseOutcome::Balanced(plug(old(up.model), rb_erase_one_child_model(old(tree.model)))));
                                    unfold(erase_out_tree(EraseOutcome::Balanced(plug(old(up.model), rb_erase_one_child_model(old(tree.model)))))); normalize();
                                }
                                have out.model == erase_outcome(old(tree.model), old(up.model)) by {
                                    rewrite(out.model, EraseOutcome::Balanced(plug(old(up.model), rb_erase_one_child_model(old(tree.model)))));
                                    rewrite(erase_outcome(old(tree.model), old(up.model)), EraseOutcome::Balanced(plug(old(up.model), rb_erase_one_child_model(old(tree.model)))));
                                    normalize();
                                }
                                have rb_tree_parent_consistent(erase_out_tree(out.model)) == 1 by {
                                    rewrite(out.model, EraseOutcome::Balanced(plug(old(up.model), rb_erase_one_child_model(old(tree.model)))));
                                    unfold(erase_out_tree(EraseOutcome::Balanced(plug(old(up.model), rb_erase_one_child_model(old(tree.model))))));
                                    rewrite(rb_erase_one_child_model(old(tree.model)), rb_reparent(rb_recolor(erased_right, Color::Black), erased_parent));
                                    close();
                                }
                                have erase_out_tree(out.model) == plug(old(up.model), erase_splice(old(tree.model))) by {
                                    rewrite(out.model, EraseOutcome::Balanced(plug(old(up.model), rb_erase_one_child_model(old(tree.model)))));
                                    unfold(erase_out_tree(EraseOutcome::Balanced(plug(old(up.model), rb_erase_one_child_model(old(tree.model))))));
                                    rewrite(erase_splice(old(tree.model)), rb_erase_one_child_model(old(tree.model)));
                                    normalize();
                                }
                                close();
                            }
                        },
                    }
                },
                RbTree::Node(el_id, el_parent, el_color, el_left, el_right) => {
                    match erased_right {
                        RbTree::Empty => {
                            // Only a left child: symmetric, but the C copies the parent word into the
                            // child before replacing the link.
                            have rb_left(old(tree.model)) == erased_left;
                            have rb_right(old(tree.model)) == RbTree::Empty;
                            have erase_outcome(old(tree.model), old(up.model)) == EraseOutcome::Balanced(plug(old(up.model), rb_erase_one_child_model(old(tree.model))));
                            have erase_splice(old(tree.model)) == rb_erase_one_child_model(old(tree.model));
                            have erased_left != RbTree::Empty;
                            have ctx_rb(up.model, black_height(RbTree::Node(erased, erased_parent, erased_color, erased_left, RbTree::Empty)),
                                rb_color(RbTree::Node(erased, erased_parent, erased_color, erased_left, RbTree::Empty))) == 1 by {
                                rewrite(RbTree::Empty, erased_right);
                                rewrite(RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right), tree.model); close();
                            }
                            apply(rb_erase_only_left_child(erased, erased_parent, erased_color, erased_left, up.model));
                            apply(ctx_consistent_node_children(up.model, erased, erased_parent, erased_color, erased_left, erased_right, 0));
                            apply(rb_erase_child_keeps_parents(up.model, erased, erased_parent, erased_color, erased_left, erased_right, erased_left));
                            apply(erase_context_parent(up.model, erased, erased_parent, erased_color, erased_left, erased_right));
                            apply(plug_parent_consistent_transport(up.model, rb_reparent(rb_recolor(erased_left, Color::Black), erased_parent), 0));
                            have rb_tree_parent_consistent(plug(old(up.model), rb_reparent(rb_recolor(erased_left, Color::Black), erased_parent))) == 1 by {
                                unfold(rb_tree_parent_consistent(plug(old(up.model), rb_reparent(rb_recolor(erased_left, Color::Black), erased_parent))));
                            }
                            have rb_reparent(rb_recolor(erased_left, Color::Black), erased_parent)
                                == RbTree::Node(el_id, erased_parent, Color::Black, el_left, el_right) by {
                                rewrite(erased_left, RbTree::Node(el_id, el_parent, el_color, el_left, el_right));
                                unfold(rb_recolor(RbTree::Node(el_id, el_parent, el_color, el_left, el_right), Color::Black));
                                unfold(rb_reparent(RbTree::Node(el_id, el_parent, Color::Black, el_left, el_right), erased_parent)); normalize();
                            }
                            have rb_erase_one_child_model(old(tree.model)) == rb_reparent(rb_recolor(erased_left, Color::Black), erased_parent) by {
                                rewrite(old(tree.model), RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right));
                                unfold(rb_erase_one_child_model(RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right)));
                                rewrite(erased_right, RbTree::Empty);
                                rewrite(erased_left, RbTree::Node(el_id, el_parent, el_color, el_left, el_right));
                                unfold(rb_erase_root_child(RbTree::Node(erased, erased_parent, erased_color, RbTree::Node(el_id, el_parent, el_color, el_left, el_right), RbTree::Empty)));
                                normalize();
                            }
                            have rb_inorder(erase_splice(old(tree.model))) == list::append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model)))) by {
                                rewrite(erase_splice(old(tree.model)), rb_erase_one_child_model(old(tree.model)));
                                rewrite(rb_erase_one_child_model(old(tree.model)), rb_reparent(rb_recolor(erased_left, Color::Black), erased_parent));
                                rewrite(rb_inorder(rb_reparent(rb_recolor(erased_left, Color::Black), erased_parent)), rb_inorder(erased_left));
                                rewrite(rb_left(old(tree.model)), erased_left); rewrite(rb_right(old(tree.model)), RbTree::Empty);
                                unfold(rb_inorder(RbTree::Empty));
                                apply(list::append_right_identity(rb_inorder(erased_left)));
                                rewrite(list::append(rb_inorder(erased_left), List<struct rb_node*>::Nil), rb_inorder(erased_left)); normalize();
                            }
                            let { left: l, right: r } = unfold(tree);
                            mark erased_left_tag;
                            unfold(r);
                            let { left: child_left, right: child_right } = unfold(l);
                            have (node->__rb_parent_color & 1) == 1 by {
                                rewrite((node->__rb_parent_color & 1), color_bit(erased_color));
                                rewrite(erased_color, Color::Black); unfold(color_bit(Color::Black)); normalize();
                            }
                            have (old(node->__rb_parent_color) & 1) == 1 by { rewrite(old(node->__rb_parent_color), node->__rb_parent_color); close(); }
                            step_until(statement(4).statement(5).statement(0).entry);
                            have *((&node->__rb_parent_color) as (int32**)) == at(erased_left_tag, *((&node->__rb_parent_color) as (int32**))) by close();
                            have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == erased_parent by close();
                            step_until(call(__rb_change_child, 1).entry);
                            have tmp == el_id by close();
                            have tmp->__rb_parent_color == pc by close();
                            have ((tmp->__rb_parent_color & ~3) as (struct rb_node *)) == erased_parent by close();
                            let replacement_tag = fold(erase_saved_parent(tmp, erased_parent), { word: pc, color: Color::Black });
                            have ctx_node_is(up.model, parent) == 1;
                            let { links: incoming, frame: outer_frame } = detach_erase_links(node, parent, root, { before: up });
                            observe(erase_callbacks(augment));
                            mark incoming_link_state;
                            let { sibling_ptr: sibling_ptr, root_count: root_count, parent_count: parent_count, tag: parent_tag, above: above } = unfold(incoming);
                            have separate(memory(root[0..root_count]), memory(*augment)) by close();
                            have separate(memory(parent[0..parent_count]), memory(*augment)) by close();
                            let incoming = fold(erase_change_links(node, parent, root), {
                                model: at(incoming_link_state, incoming.model), sibling_ptr: sibling_ptr,
                                root_count: root_count, parent_count: parent_count, tag: parent_tag, above: above
                            });
                            let { updated: linked } = step(__rb_change_child, { links: incoming });
                            have linked.model == outer_frame.model;
                            have linked.sibling_ptr == outer_frame.sibling_ptr;
                            have linked.tag == outer_frame.tag;
                            have linked.above == outer_frame.above;
                            let { updated: remaining } = attach_erase_links(tmp, parent, root, { links: linked, frame: outer_frame });
                            unfold(replacement_tag);
                            have ((tmp->__rb_parent_color & ~3) as (struct rb_node *)) == erased_parent by close();
                            have (pc & 1) == color_bit(Color::Black) by {
                                rewrite(pc, old(node->__rb_parent_color)); unfold(color_bit(Color::Black)); close();
                            }
                            let replacement = fold(rb_at(tmp), {
                                model: RbTree::Node(el_id, erased_parent, Color::Black, el_left, el_right),
                                left: child_left, right: child_right
                            });
                            have rb_tree_parent_consistent(plug(remaining.model, replacement.model)) == 1 by {
                                rewrite(remaining.model, old(up.model));
                                rewrite(replacement.model, rb_reparent(rb_recolor(erased_left, Color::Black), erased_parent));
                                unfold(rb_tree_parent_consistent(plug(old(up.model), rb_reparent(rb_recolor(erased_left, Color::Black), erased_parent))));
                                close();
                            }
                            mark balanced;
                            let { whole: whole } = refold_to_root(el_id, root, { c: remaining, t: replacement });
                            have whole.model == plug(old(up.model), rb_erase_one_child_model(old(tree.model))) by {
                                rewrite(whole.model, plug(at(balanced, remaining.model), RbTree::Node(el_id, erased_parent, Color::Black, el_left, el_right)));
                                rewrite(at(balanced, remaining.model), old(up.model));
                                rewrite(rb_erase_one_child_model(old(tree.model)), rb_reparent(rb_recolor(erased_left, Color::Black), erased_parent));
                                rewrite(rb_reparent(rb_recolor(erased_left, Color::Black), erased_parent), RbTree::Node(el_id, erased_parent, Color::Black, el_left, el_right));
                                normalize();
                            }
                            with(erase_callbacks(augment)) { step_until(function.exit); }
                            let out = fold(erase_out(root, result), { model: EraseOutcome::Balanced(plug(old(up.model), rb_erase_one_child_model(old(tree.model)))), whole: whole });
                            have erase_out_rb(out.model) == 1 by {
                                rewrite(out.model, EraseOutcome::Balanced(plug(old(up.model), rb_erase_one_child_model(old(tree.model)))));
                                unfold(erase_out_rb(EraseOutcome::Balanced(plug(old(up.model), rb_erase_one_child_model(old(tree.model))))));
                                rewrite(rb_erase_one_child_model(old(tree.model)), rb_reparent(rb_recolor(erased_left, Color::Black), erased_parent));
                                close();
                            }
                            have erase_out_tree(out.model) == plug(old(up.model), rb_erase_one_child_model(old(tree.model))) by {
                                rewrite(out.model, EraseOutcome::Balanced(plug(old(up.model), rb_erase_one_child_model(old(tree.model)))));
                                unfold(erase_out_tree(EraseOutcome::Balanced(plug(old(up.model), rb_erase_one_child_model(old(tree.model)))))); normalize();
                            }
                            have out.model == erase_outcome(old(tree.model), old(up.model)) by {
                                rewrite(out.model, EraseOutcome::Balanced(plug(old(up.model), rb_erase_one_child_model(old(tree.model)))));
                                rewrite(erase_outcome(old(tree.model), old(up.model)), EraseOutcome::Balanced(plug(old(up.model), rb_erase_one_child_model(old(tree.model)))));
                                normalize();
                            }
                            have rb_tree_parent_consistent(erase_out_tree(out.model)) == 1 by {
                                rewrite(out.model, EraseOutcome::Balanced(plug(old(up.model), rb_erase_one_child_model(old(tree.model)))));
                                unfold(erase_out_tree(EraseOutcome::Balanced(plug(old(up.model), rb_erase_one_child_model(old(tree.model))))));
                                rewrite(rb_erase_one_child_model(old(tree.model)), rb_reparent(rb_recolor(erased_left, Color::Black), erased_parent));
                                close();
                            }
                            have erase_out_tree(out.model) == plug(old(up.model), erase_splice(old(tree.model))) by {
                                rewrite(out.model, EraseOutcome::Balanced(plug(old(up.model), rb_erase_one_child_model(old(tree.model)))));
                                unfold(erase_out_tree(EraseOutcome::Balanced(plug(old(up.model), rb_erase_one_child_model(old(tree.model))))));
                                rewrite(erase_splice(old(tree.model)), rb_erase_one_child_model(old(tree.model)));
                                normalize();
                            }
                            close();
                        },
                        RbTree::Node(er_id, er_parent, er_color, er_left, er_right) => {
                            match er_left {
                                RbTree::Empty => {
                                    match er_right {
                                        RbTree::Empty => {
                                            match er_color {
                                                Color::Red => {
                                                    // Immediate red-leaf successor: it takes the erased node's place and color.
                                                    have rb_left(old(tree.model)) == erased_left;
                                                    have rb_right(old(tree.model)) == erased_right;
                                                    have erase_outcome(old(tree.model), old(up.model)) == EraseOutcome::Balanced(plug(old(up.model), rb_erase_immediate_leaf_model(old(tree.model)))) by {
                                                        rewrite(old(tree.model), RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right));
                                                        rewrite(erased_left, RbTree::Node(el_id, el_parent, el_color, el_left, el_right));
                                                        rewrite(erased_right, RbTree::Node(er_id, er_parent, er_color, er_left, er_right));
                                                        rewrite(er_left, RbTree::Empty); rewrite(er_right, RbTree::Empty); rewrite(er_color, Color::Red);
                                                        unfold(erase_outcome(RbTree::Node(erased, erased_parent, erased_color, RbTree::Node(el_id, el_parent, el_color, el_left, el_right), RbTree::Node(er_id, er_parent, Color::Red, RbTree::Empty, RbTree::Empty)), old(up.model)));
                                                        normalize();
                                                    }
                                                    have erase_splice(old(tree.model)) == rb_erase_immediate_leaf_model(old(tree.model)) by {
                                                        rewrite(old(tree.model), RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right));
                                                        rewrite(erased_left, RbTree::Node(el_id, el_parent, el_color, el_left, el_right));
                                                        rewrite(erased_right, RbTree::Node(er_id, er_parent, er_color, er_left, er_right));
                                                        rewrite(er_left, RbTree::Empty); rewrite(er_right, RbTree::Empty);
                                                        rewrite(er_color, Color::Red);
                                                        unfold(erase_splice(RbTree::Node(erased, erased_parent, erased_color, RbTree::Node(el_id, el_parent, el_color, el_left, el_right), RbTree::Node(er_id, er_parent, Color::Red, RbTree::Empty, RbTree::Empty))));
                                                        normalize();
                                                    }
                                                    have is_rb(RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right)) == 1 by {
                                                        rewrite(RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right), tree.model); close();
                                                    }
                                                    have ctx_rb(up.model, black_height(RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right)),
                                                        rb_color(RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right))) == 1 by {
                                                        rewrite(RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right), tree.model); close();
                                                    }
                                                    apply(rb_erase_red_successor_splice(erased, er_id, erased_parent, erased_color, erased_left, erased_right, up.model, 0));
                                                    apply(erase_context_parent(up.model, erased, erased_parent, erased_color, erased_left, erased_right));
                                                    have rb_successor_splice(er_id, erased_parent, erased_color, erased_left, erased_right)
                                                        == RbTree::Node(er_id, erased_parent, erased_color, RbTree::Node(el_id, er_id, el_color, el_left, el_right), RbTree::Empty) by {
                                                        unfold(rb_successor_splice(er_id, erased_parent, erased_color, erased_left, erased_right));
                                                        rewrite(erased_left, RbTree::Node(el_id, el_parent, el_color, el_left, el_right));
                                                        rewrite(erased_right, RbTree::Node(er_id, er_parent, er_color, er_left, er_right));
                                                        rewrite(er_left, RbTree::Empty); rewrite(er_right, RbTree::Empty);
                                                        unfold(rb_remove_min(RbTree::Node(er_id, er_parent, er_color, RbTree::Empty, RbTree::Empty)));
                                                        unfold(rb_reparent(RbTree::Empty, er_parent)); unfold(rb_reparent(RbTree::Empty, er_id));
                                                        unfold(rb_reparent(RbTree::Node(el_id, el_parent, el_color, el_left, el_right), er_id));
                                                        normalize();
                                                    }
                                                    have rb_erase_immediate_leaf_model(old(tree.model)) == rb_successor_splice(er_id, erased_parent, erased_color, erased_left, erased_right) by {
                                                        rewrite(old(tree.model), RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right));
                                                        rewrite(erased_right, RbTree::Node(er_id, er_parent, er_color, er_left, er_right));
                                                        unfold(rb_erase_immediate_leaf_model(RbTree::Node(erased, erased_parent, erased_color, erased_left, RbTree::Node(er_id, er_parent, er_color, er_left, er_right))));
                                                        normalize();
                                                    }
                                                    have rb_inorder(erase_splice(old(tree.model))) == list::append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model)))) by {
                                                        rewrite(erase_splice(old(tree.model)), rb_erase_immediate_leaf_model(old(tree.model)));
                                                        rewrite(rb_erase_immediate_leaf_model(old(tree.model)), rb_successor_splice(er_id, erased_parent, erased_color, erased_left, erased_right));
                                                        rewrite(rb_left(old(tree.model)), erased_left); rewrite(rb_right(old(tree.model)), erased_right); close();
                                                    }
                                                    have rb_tree_parent_consistent(plug(old(up.model), rb_successor_splice(er_id, erased_parent, erased_color, erased_left, erased_right))) == 1 by {
                                                        unfold(rb_tree_parent_consistent(plug(old(up.model), rb_successor_splice(er_id, erased_parent, erased_color, erased_left, erased_right))));
                                                    }
                                                    have is_rb_root(plug(old(up.model), rb_successor_splice(er_id, erased_parent, erased_color, erased_left, erased_right))) == 1 by {
                                                        rewrite(old(up.model), up.model); close();
                                                    }
                                                    let { left: l, right: r } = unfold(tree);
                                                    let old_left = fold(erase_saved_left(node), { child: node->rb_left });
                                                    let { left: sleft, right: sright } = unfold(r);
                                                    unfold(sleft); unfold(sright);
                                                    let { left: lleft, right: lright } = unfold(l);
                                                    have (er_id->__rb_parent_color & 1) == 0 by {
                                                        rewrite((er_id->__rb_parent_color & 1), color_bit(er_color));
                                                        rewrite(er_color, Color::Red); unfold(color_bit(Color::Red)); normalize();
                                                    }
                                                    have (old(node->__rb_parent_color) & 1) == color_bit(erased_color) by {
                                                        rewrite(old(node->__rb_parent_color), node->__rb_parent_color); close();
                                                    }
                                                    have old(node->__rb_parent_color) == address(erased_parent) + (old(node->__rb_parent_color) & 1) by {
                                                        rewrite(old(node->__rb_parent_color), node->__rb_parent_color); close();
                                                    }
                                                    let successor_color = fold(erase_saved_color(er_id), { color: er_color });
                                                    let erased_tag = fold(erase_saved_parent(node, erased_parent), { word: node->__rb_parent_color, color: erased_color });
                                                    let left_color = fold(erase_saved_color(el_id), { color: el_color });
                                                    mark before_left_splice;
                                                    let left_children = fold(erase_saved_children(el_id), { left: el_id->rb_left, right: el_id->rb_right });
                                                    with(erase_callbacks(augment)) { step_until(assignment(tmp, 5).entry); }
                                                    unfold(old_left);
                                                    have node->rb_left == el_id by close();
                                                    step(); step();
                                                    unfold(left_color);
                                                    mark before_left_reparent;
                                                    have (tmp->__rb_parent_color & 1) == color_bit(el_color) by close();
                                                    step();
                                                    have at(before_left_reparent, successor->rb_left) == el_id by close();
                                                    have contains(memory(el_id->__rb_parent_color), region(43).footprint) by close();
                                                    have separate(memory(el_id->__rb_parent_color), memory(successor->rb_left)) by close();
                                                    apply(click::separation::contains_refl(memory(successor->rb_left)));
                                                    apply(click::separation::separate_restrict(memory(el_id->__rb_parent_color), memory(successor->rb_left), region(43).footprint, memory(successor->rb_left)));
                                                    have successor->rb_left == at(before_left_reparent, successor->rb_left) by {
                                                        preserve(memory(successor->rb_left), region(43));
                                                    }
                                                    have successor->rb_left == el_id by close();
                                                    have successor->rb_right == 0 by close();
                                                    let successor_links = fold(erase_saved_children(successor), { left: el_id, right: successor->rb_right });
                                                    have aligned(successor, 8) by close();
                                                    have ((tmp->__rb_parent_color & ~3) as (struct rb_node *)) == successor by {
                                                        close() using {
                                                            aligned(successor, 8);
                                                            aligned(successor, 8) implies ((tmp->__rb_parent_color & ~3) as (struct rb_node *)) == successor;
                                                        };
                                                    }
                                                    apply(packed_parent_word(successor, at(before_left_reparent, tmp->__rb_parent_color)));
                                                    have tmp->__rb_parent_color == address(successor) + (tmp->__rb_parent_color & 1) by {
                                                        rewrite(tmp->__rb_parent_color, ((at(before_left_reparent, tmp->__rb_parent_color) & 1) | address(successor)));
                                                        close();
                                                    }
                                                    have (tmp->__rb_parent_color & 1) == color_bit(el_color) by {
                                                        rewrite(tmp->__rb_parent_color, ((at(before_left_reparent, tmp->__rb_parent_color) & 1) | address(successor)));
                                                        rewrite(((at(before_left_reparent, tmp->__rb_parent_color) & 1) | address(successor)) & 1,
                                                            at(before_left_reparent, tmp->__rb_parent_color) & 1);
                                                        close();
                                                    }
                                                    let moved_parent = fold(erase_saved_parent(tmp, successor), {
                                                        word: tmp->__rb_parent_color, color: el_color
                                                    });
                                                    unfold(left_children);
                                                    unfold(moved_parent);
                                                    have tmp->rb_left == at(before_left_splice, el_id->rb_left) by close();
                                                    have tmp->rb_right == at(before_left_splice, el_id->rb_right) by close();
                                                    let moved_left = fold(rb_at(tmp), {
                                                        model: RbTree::Node(el_id, successor, el_color, el_left, el_right),
                                                        left: lleft, right: lright
                                                    });
                                                    let empty_right = fold(rb_at(0), { model: RbTree::Empty });
                                                    have rb_parent_is(RbTree::Node(el_id, er_id, el_color, el_left, el_right), er_id) == 1 by {
                                                        unfold(rb_parent_is(RbTree::Node(el_id, er_id, el_color, el_left, el_right), er_id)); normalize();
                                                    }
                                                    have rb_parent_is(RbTree::Empty, er_id) == 1 by { unfold(rb_parent_is(RbTree::Empty, er_id)); normalize(); }
                                                    unfold(erased_tag);
                                                    have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == erased_parent by close();
                                                    step_until(call(__rb_change_child, 2).entry);
                                                    have tmp == erased_parent;
                                                    mark transplant;
                                                    have ctx_node_is(up.model, tmp) == 1;
                                                    let { links: incoming, frame: outer_frame } = detach_erase_links(node, tmp, root, { before: up });
                                                    observe(erase_callbacks(augment));
                                                    mark incoming_link_state;
                                                    let { sibling_ptr: sibling_ptr, root_count: root_count, parent_count: parent_count, tag: parent_tag, above: above } = unfold(incoming);
                                                    have separate(memory(root[0..root_count]), memory(*augment)) by close();
                                                    have separate(memory(tmp[0..parent_count]), memory(*augment)) by close();
                                                    let incoming = fold(erase_change_links(node, tmp, root), {
                                                        model: at(incoming_link_state, incoming.model), sibling_ptr: sibling_ptr,
                                                        root_count: root_count, parent_count: parent_count, tag: parent_tag, above: above
                                                    });
                                                    let { updated: linked } = step(__rb_change_child, { links: incoming });
                                                    have linked.model == outer_frame.model;
                                                    have linked.sibling_ptr == outer_frame.sibling_ptr;
                                                    have linked.tag == outer_frame.tag;
                                                    have linked.above == outer_frame.above;
                                                    let { updated: remaining } = attach_erase_links(successor, tmp, root, { links: linked, frame: outer_frame });
                                                    have successor == er_id;
                                                    unfold(successor_color);
                                                    have (er_id->__rb_parent_color & 1) == color_bit(er_color) by close();
                                                    have (successor->__rb_parent_color & 1) == 0 by {
                                                        rewrite(successor, er_id);
                                                        rewrite((er_id->__rb_parent_color & 1), color_bit(er_color));
                                                        rewrite(er_color, Color::Red);
                                                        unfold(color_bit(Color::Red)); normalize();
                                                    }
                                                    step_until(statement(4).statement(5).statement(15).entry);
                                                    mark before_copying_tag;
                                                    have ((pc & ~3) as (struct rb_node *)) == erased_parent by close();
                                                    step();
                                                    have successor->__rb_parent_color == at(before_copying_tag, pc) by close();
                                                    have ((successor->__rb_parent_color & ~3) as (struct rb_node *)) == erased_parent by close();
                                                    let replacement_tag = fold(erase_saved_parent(successor, erased_parent), { word: at(before_copying_tag, pc), color: erased_color });
                                                    step_until(statement(5).entry);
                                                    unfold(successor_links);
                                                    unfold(replacement_tag);
                                                    have tmp == er_id by close();
                                                    have tmp->rb_left == el_id by close();
                                                    have tmp->rb_right == 0 by close();
                                                    have ((tmp->__rb_parent_color & ~3) as (struct rb_node *)) == erased_parent by close();
                                                    let replacement = fold(rb_at(tmp), {
                                                        model: RbTree::Node(tmp, erased_parent, erased_color, RbTree::Node(el_id, er_id, el_color, el_left, el_right), RbTree::Empty),
                                                        left: moved_left, right: empty_right
                                                    });
                                                    have rb_tree_parent_consistent(plug(remaining.model, replacement.model)) == 1 by {
                                                        rewrite(remaining.model, old(up.model));
                                                        rewrite(replacement.model, RbTree::Node(er_id, erased_parent, erased_color, RbTree::Node(el_id, er_id, el_color, el_left, el_right), RbTree::Empty));
                                                        rewrite(RbTree::Node(er_id, erased_parent, erased_color, RbTree::Node(el_id, er_id, el_color, el_left, el_right), RbTree::Empty), rb_successor_splice(er_id, erased_parent, erased_color, erased_left, erased_right));
                                                        close();
                                                    }
                                                    mark balanced;
                                                    let { whole: whole } = refold_to_root(er_id, root, { c: remaining, t: replacement });
                                                    have whole.model == plug(old(up.model), rb_erase_immediate_leaf_model(old(tree.model))) by {
                                                        rewrite(whole.model, plug(at(balanced, remaining.model), RbTree::Node(er_id, erased_parent, erased_color, RbTree::Node(el_id, er_id, el_color, el_left, el_right), RbTree::Empty)));
                                                        rewrite(at(balanced, remaining.model), old(up.model));
                                                        rewrite(rb_erase_immediate_leaf_model(old(tree.model)), rb_successor_splice(er_id, erased_parent, erased_color, erased_left, erased_right));
                                                        rewrite(rb_successor_splice(er_id, erased_parent, erased_color, erased_left, erased_right), RbTree::Node(er_id, erased_parent, erased_color, RbTree::Node(el_id, er_id, el_color, el_left, el_right), RbTree::Empty));
                                                        normalize();
                                                    }
                                                    with(erase_callbacks(augment)) { step_until(function.exit); }
                                                    let out = fold(erase_out(root, result), { model: EraseOutcome::Balanced(plug(old(up.model), rb_erase_immediate_leaf_model(old(tree.model)))), whole: whole });
                                                    have erase_out_rb(out.model) == 1 by {
                                                        rewrite(out.model, EraseOutcome::Balanced(plug(old(up.model), rb_erase_immediate_leaf_model(old(tree.model)))));
                                                        unfold(erase_out_rb(EraseOutcome::Balanced(plug(old(up.model), rb_erase_immediate_leaf_model(old(tree.model))))));
                                                        rewrite(rb_erase_immediate_leaf_model(old(tree.model)), rb_successor_splice(er_id, erased_parent, erased_color, erased_left, erased_right));
                                                        close();
                                                    }
                                                    have erase_out_tree(out.model) == plug(old(up.model), rb_erase_immediate_leaf_model(old(tree.model))) by {
                                                        rewrite(out.model, EraseOutcome::Balanced(plug(old(up.model), rb_erase_immediate_leaf_model(old(tree.model)))));
                                                        unfold(erase_out_tree(EraseOutcome::Balanced(plug(old(up.model), rb_erase_immediate_leaf_model(old(tree.model)))))); normalize();
                                                    }
                                                    have out.model == erase_outcome(old(tree.model), old(up.model)) by {
                                                        rewrite(out.model, EraseOutcome::Balanced(plug(old(up.model), rb_erase_immediate_leaf_model(old(tree.model)))));
                                                        rewrite(erase_outcome(old(tree.model), old(up.model)), EraseOutcome::Balanced(plug(old(up.model), rb_erase_immediate_leaf_model(old(tree.model)))));
                                                        normalize();
                                                    }
                                                    have rb_tree_parent_consistent(erase_out_tree(out.model)) == 1 by {
                                                        rewrite(out.model, EraseOutcome::Balanced(plug(old(up.model), rb_erase_immediate_leaf_model(old(tree.model)))));
                                                        unfold(erase_out_tree(EraseOutcome::Balanced(plug(old(up.model), rb_erase_immediate_leaf_model(old(tree.model))))));
                                                        rewrite(rb_erase_immediate_leaf_model(old(tree.model)), rb_successor_splice(er_id, erased_parent, erased_color, erased_left, erased_right));
                                                        close();
                                                    }
                                                    have erase_out_tree(out.model) == plug(old(up.model), erase_splice(old(tree.model))) by {
                                                        rewrite(out.model, EraseOutcome::Balanced(plug(old(up.model), rb_erase_immediate_leaf_model(old(tree.model)))));
                                                        unfold(erase_out_tree(EraseOutcome::Balanced(plug(old(up.model), rb_erase_immediate_leaf_model(old(tree.model))))));
                                                        rewrite(erase_splice(old(tree.model)), rb_erase_immediate_leaf_model(old(tree.model)));
                                                        normalize();
                                                    }
                                                    close();
                                                },
                                                Color::Black => {
                                                    // Immediate black-leaf successor: it takes the erased node's place and color,
                                                    // leaving an empty right hole one black level short; repair starts there.
                                                    have rb_left(old(tree.model)) == erased_left;
                                                    have rb_right(old(tree.model)) == erased_right;
                                                    have erase_outcome(old(tree.model), old(up.model)) == EraseOutcome::Deficit(rb_erase_immediate_black_context(old(tree.model), old(up.model))) by {
                                                        rewrite(old(tree.model), RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right));
                                                        rewrite(erased_left, RbTree::Node(el_id, el_parent, el_color, el_left, el_right));
                                                        rewrite(erased_right, RbTree::Node(er_id, er_parent, er_color, er_left, er_right));
                                                        rewrite(er_left, RbTree::Empty); rewrite(er_right, RbTree::Empty);
                                                        rewrite(er_color, Color::Black);
                                                        unfold(erase_outcome(RbTree::Node(erased, erased_parent, erased_color, RbTree::Node(el_id, el_parent, el_color, el_left, el_right), RbTree::Node(er_id, er_parent, Color::Black, RbTree::Empty, RbTree::Empty)), old(up.model)));
                                                        normalize();
                                                    }
                                                    have erase_splice(old(tree.model)) == rb_erase_immediate_leaf_model(old(tree.model)) by {
                                                        rewrite(old(tree.model), RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right));
                                                        rewrite(erased_left, RbTree::Node(el_id, el_parent, el_color, el_left, el_right));
                                                        rewrite(erased_right, RbTree::Node(er_id, er_parent, er_color, er_left, er_right));
                                                        rewrite(er_left, RbTree::Empty); rewrite(er_right, RbTree::Empty);
                                                        rewrite(er_color, Color::Black);
                                                        unfold(erase_splice(RbTree::Node(erased, erased_parent, erased_color, RbTree::Node(el_id, el_parent, el_color, el_left, el_right), RbTree::Node(er_id, er_parent, Color::Black, RbTree::Empty, RbTree::Empty))));
                                                        normalize();
                                                    }
                                                    have is_rb(RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right)) == 1 by {
                                                        rewrite(RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right), tree.model); close();
                                                    }
                                                    have ctx_rb(up.model, black_height(RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right)),
                                                        rb_color(RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right))) == 1 by {
                                                        rewrite(RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right), tree.model); close();
                                                    }
                                                    apply(rb_erase_black_successor_splice(erased, er_id, erased_parent, erased_color, erased_left, erased_right, up.model, 0));
                                                    apply(erase_context_parent(up.model, erased, erased_parent, erased_color, erased_left, erased_right));
                                                    have rb_successor_splice(er_id, erased_parent, erased_color, erased_left, erased_right)
                                                        == RbTree::Node(er_id, erased_parent, erased_color, RbTree::Node(el_id, er_id, el_color, el_left, el_right), RbTree::Empty) by {
                                                        unfold(rb_successor_splice(er_id, erased_parent, erased_color, erased_left, erased_right));
                                                        rewrite(erased_left, RbTree::Node(el_id, el_parent, el_color, el_left, el_right));
                                                        rewrite(erased_right, RbTree::Node(er_id, er_parent, er_color, er_left, er_right));
                                                        rewrite(er_left, RbTree::Empty); rewrite(er_right, RbTree::Empty);
                                                        unfold(rb_remove_min(RbTree::Node(er_id, er_parent, er_color, RbTree::Empty, RbTree::Empty)));
                                                        unfold(rb_reparent(RbTree::Empty, er_parent)); unfold(rb_reparent(RbTree::Empty, er_id));
                                                        unfold(rb_reparent(RbTree::Node(el_id, el_parent, el_color, el_left, el_right), er_id));
                                                        normalize();
                                                    }
                                                    have rb_erase_immediate_leaf_model(old(tree.model)) == rb_successor_splice(er_id, erased_parent, erased_color, erased_left, erased_right) by {
                                                        rewrite(old(tree.model), RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right));
                                                        rewrite(erased_right, RbTree::Node(er_id, er_parent, er_color, er_left, er_right));
                                                        unfold(rb_erase_immediate_leaf_model(RbTree::Node(erased, erased_parent, erased_color, erased_left, RbTree::Node(er_id, er_parent, er_color, er_left, er_right))));
                                                        normalize();
                                                    }
                                                    have rb_inorder(erase_splice(old(tree.model))) == list::append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model)))) by {
                                                        rewrite(erase_splice(old(tree.model)), rb_erase_immediate_leaf_model(old(tree.model)));
                                                        rewrite(rb_erase_immediate_leaf_model(old(tree.model)), rb_successor_splice(er_id, erased_parent, erased_color, erased_left, erased_right));
                                                        rewrite(rb_left(old(tree.model)), erased_left); rewrite(rb_right(old(tree.model)), erased_right); close();
                                                    }
                                                    have rb_successor_context(er_id, erased_parent, erased_color, erased_left, erased_right, old(up.model))
                                                        == Context::Right(er_id, erased_parent, erased_color, RbTree::Node(el_id, er_id, el_color, el_left, el_right), old(up.model)) by {
                                                        unfold(rb_successor_context(er_id, erased_parent, erased_color, erased_left, erased_right, old(up.model)));
                                                        rewrite(erased_left, RbTree::Node(el_id, el_parent, el_color, el_left, el_right));
                                                        rewrite(erased_right, RbTree::Node(er_id, er_parent, er_color, er_left, er_right));
                                                        unfold(rb_reparent(RbTree::Node(er_id, er_parent, er_color, er_left, er_right), er_id));
                                                        rewrite(er_left, RbTree::Empty);
                                                        unfold(rb_min_context(RbTree::Node(er_id, er_id, er_color, RbTree::Empty, er_right),
                                                            Context::Right(er_id, erased_parent, erased_color, rb_reparent(RbTree::Node(el_id, el_parent, el_color, el_left, el_right), er_id), old(up.model))));
                                                        unfold(rb_reparent(RbTree::Node(el_id, el_parent, el_color, el_left, el_right), er_id)); normalize();
                                                    }
                                                    have rb_erase_immediate_black_context(old(tree.model), old(up.model))
                                                        == rb_successor_context(er_id, erased_parent, erased_color, erased_left, erased_right, old(up.model)) by {
                                                        rewrite(old(tree.model), RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right));
                                                        rewrite(erased_right, RbTree::Node(er_id, er_parent, er_color, er_left, er_right));
                                                        unfold(rb_erase_immediate_black_context(RbTree::Node(erased, erased_parent, erased_color, erased_left, RbTree::Node(er_id, er_parent, er_color, er_left, er_right)), old(up.model)));
                                                        normalize();
                                                    }
                                                    have ctx_rb(rb_successor_context(er_id, erased_parent, erased_color, erased_left, erased_right, old(up.model)), Nat::Succ(Nat::Zero), Color::Black) == 1 by {
                                                        rewrite(old(up.model), up.model); close();
                                                    }
                                                    have plug(rb_successor_context(er_id, erased_parent, erased_color, erased_left, erased_right, old(up.model)), RbTree::Empty)
                                                        == plug(old(up.model), rb_successor_splice(er_id, erased_parent, erased_color, erased_left, erased_right)) by {
                                                        rewrite(old(up.model), up.model); close();
                                                    }
                                                    apply(plug_parent_consistent_transport(rb_successor_context(er_id, erased_parent, erased_color, erased_left, erased_right, old(up.model)), RbTree::Empty, 0));
                                                    have rb_tree_parent_consistent(plug(rb_successor_context(er_id, erased_parent, erased_color, erased_left, erased_right, old(up.model)), RbTree::Empty)) == 1 by {
                                                        unfold(rb_tree_parent_consistent(plug(rb_successor_context(er_id, erased_parent, erased_color, erased_left, erased_right, old(up.model)), RbTree::Empty)));
                                                    }
                                                    have ctx_node_is(old(up.model), erased_parent) == 1 by { rewrite(old(up.model), up.model); close(); }
                                                    have old(up.model) == ctx_reroot(old(up.model), erased_parent) by { rewrite(old(up.model), up.model); close(); }
                                                    let { left: l, right: r } = unfold(tree);
                                                    let old_left = fold(erase_saved_left(node), { child: node->rb_left });
                                                    let { left: sleft, right: sright } = unfold(r);
                                                    unfold(sleft); unfold(sright);
                                                    let { left: lleft, right: lright } = unfold(l);
                                                    have (er_id->__rb_parent_color & 1) == 1 by {
                                                        rewrite((er_id->__rb_parent_color & 1), color_bit(er_color));
                                                        rewrite(er_color, Color::Black); unfold(color_bit(Color::Black)); normalize();
                                                    }
                                                    have (old(node->__rb_parent_color) & 1) == color_bit(erased_color) by {
                                                        rewrite(old(node->__rb_parent_color), node->__rb_parent_color); close();
                                                    }
                                                    have old(node->__rb_parent_color) == address(erased_parent) + (old(node->__rb_parent_color) & 1) by {
                                                        rewrite(old(node->__rb_parent_color), node->__rb_parent_color); close();
                                                    }
                                                    let successor_color = fold(erase_saved_color(er_id), { color: er_color });
                                                    let erased_tag = fold(erase_saved_parent(node, erased_parent), { word: node->__rb_parent_color, color: erased_color });
                                                    let left_color = fold(erase_saved_color(el_id), { color: el_color });
                                                    mark before_left_splice;
                                                    let left_children = fold(erase_saved_children(el_id), { left: el_id->rb_left, right: el_id->rb_right });
                                                    with(erase_callbacks(augment)) { step_until(assignment(tmp, 5).entry); }
                                                    unfold(old_left);
                                                    have node->rb_left == el_id by close();
                                                    step(); step();
                                                    unfold(left_color);
                                                    mark before_left_reparent;
                                                    have (tmp->__rb_parent_color & 1) == color_bit(el_color) by close();
                                                    step();
                                                    have at(before_left_reparent, successor->rb_left) == el_id by close();
                                                    have contains(memory(el_id->__rb_parent_color), region(43).footprint) by close();
                                                    have separate(memory(el_id->__rb_parent_color), memory(successor->rb_left)) by close();
                                                    apply(click::separation::contains_refl(memory(successor->rb_left)));
                                                    apply(click::separation::separate_restrict(memory(el_id->__rb_parent_color), memory(successor->rb_left), region(43).footprint, memory(successor->rb_left)));
                                                    have successor->rb_left == at(before_left_reparent, successor->rb_left) by {
                                                        preserve(memory(successor->rb_left), region(43));
                                                    }
                                                    have successor->rb_left == el_id by close();
                                                    have successor->rb_right == 0 by close();
                                                    let successor_links = fold(erase_saved_children(successor), { left: el_id, right: successor->rb_right });
                                                    have aligned(successor, 8) by close();
                                                    have ((tmp->__rb_parent_color & ~3) as (struct rb_node *)) == successor by {
                                                        close() using {
                                                            aligned(successor, 8);
                                                            aligned(successor, 8) implies ((tmp->__rb_parent_color & ~3) as (struct rb_node *)) == successor;
                                                        };
                                                    }
                                                    apply(packed_parent_word(successor, at(before_left_reparent, tmp->__rb_parent_color)));
                                                    have tmp->__rb_parent_color == address(successor) + (tmp->__rb_parent_color & 1) by {
                                                        rewrite(tmp->__rb_parent_color, ((at(before_left_reparent, tmp->__rb_parent_color) & 1) | address(successor)));
                                                        close();
                                                    }
                                                    have (tmp->__rb_parent_color & 1) == color_bit(el_color) by {
                                                        rewrite(tmp->__rb_parent_color, ((at(before_left_reparent, tmp->__rb_parent_color) & 1) | address(successor)));
                                                        rewrite(((at(before_left_reparent, tmp->__rb_parent_color) & 1) | address(successor)) & 1,
                                                            at(before_left_reparent, tmp->__rb_parent_color) & 1);
                                                        close();
                                                    }
                                                    let moved_parent = fold(erase_saved_parent(tmp, successor), {
                                                        word: tmp->__rb_parent_color, color: el_color
                                                    });
                                                    unfold(left_children);
                                                    unfold(moved_parent);
                                                    have tmp->rb_left == at(before_left_splice, el_id->rb_left) by close();
                                                    have tmp->rb_right == at(before_left_splice, el_id->rb_right) by close();
                                                    let moved_left = fold(rb_at(tmp), {
                                                        model: RbTree::Node(el_id, successor, el_color, el_left, el_right),
                                                        left: lleft, right: lright
                                                    });
                                                    let empty_right = fold(rb_at(0), { model: RbTree::Empty });
                                                    have rb_parent_is(RbTree::Node(el_id, er_id, el_color, el_left, el_right), er_id) == 1 by {
                                                        unfold(rb_parent_is(RbTree::Node(el_id, er_id, el_color, el_left, el_right), er_id)); normalize();
                                                    }
                                                    have rb_parent_is(RbTree::Empty, er_id) == 1 by { unfold(rb_parent_is(RbTree::Empty, er_id)); normalize(); }
                                                    unfold(erased_tag);
                                                    have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == erased_parent by close();
                                                    step_until(call(__rb_change_child, 2).entry);
                                                    have tmp == erased_parent;
                                                    mark transplant;
                                                    have ctx_node_is(up.model, tmp) == 1;
                                                    let { links: incoming, frame: outer_frame } = detach_erase_links(node, tmp, root, { before: up });
                                                    observe(erase_callbacks(augment));
                                                    mark incoming_link_state;
                                                    let { sibling_ptr: sibling_ptr, root_count: root_count, parent_count: parent_count, tag: parent_tag, above: above } = unfold(incoming);
                                                    have separate(memory(root[0..root_count]), memory(*augment)) by close();
                                                    have separate(memory(tmp[0..parent_count]), memory(*augment)) by close();
                                                    let incoming = fold(erase_change_links(node, tmp, root), {
                                                        model: at(incoming_link_state, incoming.model), sibling_ptr: sibling_ptr,
                                                        root_count: root_count, parent_count: parent_count, tag: parent_tag, above: above
                                                    });
                                                    let { updated: linked } = step(__rb_change_child, { links: incoming });
                                                    have linked.model == outer_frame.model;
                                                    have linked.sibling_ptr == outer_frame.sibling_ptr;
                                                    have linked.tag == outer_frame.tag;
                                                    have linked.above == outer_frame.above;
                                                    let { updated: remaining } = attach_erase_links(successor, tmp, root, { links: linked, frame: outer_frame });
                                                    have successor == er_id;
                                                    unfold(successor_color);
                                                    have (er_id->__rb_parent_color & 1) == color_bit(er_color) by close();
                                                    have (successor->__rb_parent_color & 1) == 1 by {
                                                        rewrite(successor, er_id);
                                                        rewrite((er_id->__rb_parent_color & 1), color_bit(er_color));
                                                        rewrite(er_color, Color::Black);
                                                        unfold(color_bit(Color::Black)); normalize();
                                                    }
                                                    step_until(statement(4).statement(5).statement(15).entry);
                                                    mark before_copying_tag;
                                                    have ((pc & ~3) as (struct rb_node *)) == erased_parent by close();
                                                    step();
                                                    have successor->__rb_parent_color == at(before_copying_tag, pc) by close();
                                                    have ((successor->__rb_parent_color & ~3) as (struct rb_node *)) == erased_parent by close();
                                                    let replacement_tag = fold(erase_saved_parent(successor, erased_parent), { word: at(before_copying_tag, pc), color: erased_color });
                                                    step_until(statement(5).entry);
                                                    unfold(successor_links);
                                                    unfold(replacement_tag);
                                                    have tmp == er_id by close();
                                                    have tmp->rb_left == el_id by close();
                                                    have tmp->rb_right == 0 by close();
                                                    have ((tmp->__rb_parent_color & ~3) as (struct rb_node *)) == erased_parent by close();
                                                    have remaining.model == old(up.model) by close();
                                                    have child == er_id by { rewrite(er_id, tmp); close(); }
                                                    have moved_left.model == RbTree::Node(el_id, er_id, el_color, el_left, el_right) by {
                                                        rewrite(er_id, child); close();
                                                    }
                                                    have ctx_node_is(remaining.model, erased_parent) == 1 by {
                                                        rewrite(remaining.model, old(up.model)); close();
                                                    }
                                                    let deficit = fold(ctx_at(0, root), {
                                                        model: Context::Right(tmp, erased_parent, erased_color, RbTree::Node(el_id, er_id, el_color, el_left, el_right), old(up.model)),
                                                        sibling: moved_left, up: remaining
                                                    });
                                                    have deficit.model == Context::Right(er_id, erased_parent, erased_color, RbTree::Node(el_id, er_id, el_color, el_left, el_right), old(up.model)) by {
                                                        rewrite(deficit.model, Context::Right(tmp, erased_parent, erased_color, RbTree::Node(el_id, er_id, el_color, el_left, el_right), old(up.model)));
                                                        rewrite(tmp, er_id); normalize();
                                                    }
                                                    have deficit.model == rb_erase_immediate_black_context(old(tree.model), old(up.model)) by {
                                                        rewrite(rb_erase_immediate_black_context(old(tree.model), old(up.model)), rb_successor_context(er_id, erased_parent, erased_color, erased_left, erased_right, old(up.model)));
                                                        rewrite(rb_successor_context(er_id, erased_parent, erased_color, erased_left, erased_right, old(up.model)), Context::Right(er_id, erased_parent, erased_color, RbTree::Node(el_id, er_id, el_color, el_left, el_right), old(up.model)));
                                                        close();
                                                    }
                                                    unfold(empty_right);
                                                    with(erase_callbacks(augment)) { step_until(function.exit); }
                                                    have result == er_id;
                                                    have deficit.model != Context::Top by {
                                                        rewrite(deficit.model, Context::Right(er_id, erased_parent, erased_color, RbTree::Node(el_id, er_id, el_color, el_left, el_right), old(up.model))); normalize();
                                                    }
                                                    have ctx_node_is(deficit.model, result) == 1 by {
                                                        rewrite(deficit.model, Context::Right(er_id, erased_parent, erased_color, RbTree::Node(el_id, er_id, el_color, el_left, el_right), old(up.model))); rewrite(result, er_id);
                                                        unfold(ctx_node_is(Context::Right(er_id, erased_parent, erased_color, RbTree::Node(el_id, er_id, el_color, el_left, el_right), old(up.model)), er_id)); normalize();
                                                    }
                                                    have rb_erase_immediate_black_context(old(tree.model), old(up.model)) != Context::Top by { rewrite(rb_erase_immediate_black_context(old(tree.model), old(up.model)), deficit.model); close(); }
                                                    have ctx_node_is(rb_erase_immediate_black_context(old(tree.model), old(up.model)), result) == 1 by { rewrite(rb_erase_immediate_black_context(old(tree.model), old(up.model)), deficit.model); close(); }
                                                    let out = fold(erase_out(root, result), { model: EraseOutcome::Deficit(rb_erase_immediate_black_context(old(tree.model), old(up.model))), deficit: deficit });
                                                    have erase_out_rb(out.model) == 1 by {
                                                        rewrite(out.model, EraseOutcome::Deficit(rb_erase_immediate_black_context(old(tree.model), old(up.model))));
                                                        unfold(erase_out_rb(EraseOutcome::Deficit(rb_erase_immediate_black_context(old(tree.model), old(up.model)))));
                                                        rewrite(rb_erase_immediate_black_context(old(tree.model), old(up.model)), rb_successor_context(er_id, erased_parent, erased_color, erased_left, erased_right, old(up.model)));
                                                        close();
                                                    }
                                                    have erase_out_tree(out.model) == plug(old(up.model), rb_erase_immediate_leaf_model(old(tree.model))) by {
                                                        rewrite(out.model, EraseOutcome::Deficit(rb_erase_immediate_black_context(old(tree.model), old(up.model))));
                                                        unfold(erase_out_tree(EraseOutcome::Deficit(rb_erase_immediate_black_context(old(tree.model), old(up.model)))));
                                                        rewrite(rb_erase_immediate_black_context(old(tree.model), old(up.model)), rb_successor_context(er_id, erased_parent, erased_color, erased_left, erased_right, old(up.model)));
                                                        rewrite(rb_erase_immediate_leaf_model(old(tree.model)), rb_successor_splice(er_id, erased_parent, erased_color, erased_left, erased_right));
                                                        close();
                                                    }
                                                    have rb_tree_parent_consistent(erase_out_tree(out.model)) == 1 by {
                                                        rewrite(out.model, EraseOutcome::Deficit(rb_erase_immediate_black_context(old(tree.model), old(up.model))));
                                                        unfold(erase_out_tree(EraseOutcome::Deficit(rb_erase_immediate_black_context(old(tree.model), old(up.model)))));
                                                        rewrite(rb_erase_immediate_black_context(old(tree.model), old(up.model)), rb_successor_context(er_id, erased_parent, erased_color, erased_left, erased_right, old(up.model)));
                                                        close();
                                                    }
                                                    have out.model == erase_outcome(old(tree.model), old(up.model)) by {
                                                        rewrite(out.model, EraseOutcome::Deficit(rb_erase_immediate_black_context(old(tree.model), old(up.model))));
                                                        rewrite(erase_outcome(old(tree.model), old(up.model)), EraseOutcome::Deficit(rb_erase_immediate_black_context(old(tree.model), old(up.model))));
                                                        normalize();
                                                    }
                                                    have rb_tree_parent_consistent(erase_out_tree(out.model)) == 1 by {
                                                        rewrite(out.model, EraseOutcome::Deficit(rb_erase_immediate_black_context(old(tree.model), old(up.model))));
                                                        unfold(erase_out_tree(EraseOutcome::Deficit(rb_erase_immediate_black_context(old(tree.model), old(up.model)))));
                                                        rewrite(rb_erase_immediate_black_context(old(tree.model), old(up.model)), rb_successor_context(er_id, erased_parent, erased_color, erased_left, erased_right, old(up.model)));
                                                        close();
                                                    }
                                                    have erase_out_tree(out.model) == plug(old(up.model), erase_splice(old(tree.model))) by {
                                                        rewrite(out.model, EraseOutcome::Deficit(rb_erase_immediate_black_context(old(tree.model), old(up.model))));
                                                        unfold(erase_out_tree(EraseOutcome::Deficit(rb_erase_immediate_black_context(old(tree.model), old(up.model)))));
                                                        rewrite(erase_splice(old(tree.model)), rb_erase_immediate_leaf_model(old(tree.model)));
                                                        rewrite(rb_erase_immediate_black_context(old(tree.model), old(up.model)), rb_successor_context(er_id, erased_parent, erased_color, erased_left, erased_right, old(up.model)));
                                                        rewrite(rb_erase_immediate_leaf_model(old(tree.model)), rb_successor_splice(er_id, erased_parent, erased_color, erased_left, erased_right));
                                                        rewrite(plug(rb_successor_context(er_id, erased_parent, erased_color, erased_left, erased_right, old(up.model)), RbTree::Empty), plug(old(up.model), rb_successor_splice(er_id, erased_parent, erased_color, erased_left, erased_right)));
                                                        normalize();
                                                    }
                                                    close();
                                                },
                                            }
                                        },
                                        RbTree::Node(ec_id, ec_parent, ec_color, ec_left, ec_right) => {
                                            // Immediate successor with a right child: the successor takes the erased
                                            // node's place and color; its child is blackened, so no repair is needed.
                                            have rb_left(old(tree.model)) == erased_left;
                                            have rb_right(old(tree.model)) == erased_right;
                                            have erase_outcome(old(tree.model), old(up.model)) == EraseOutcome::Balanced(plug(old(up.model), rb_erase_immediate_child_model(old(tree.model)))) by {
                                                rewrite(old(tree.model), RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right));
                                                rewrite(erased_left, RbTree::Node(el_id, el_parent, el_color, el_left, el_right));
                                                rewrite(erased_right, RbTree::Node(er_id, er_parent, er_color, er_left, er_right));
                                                rewrite(er_left, RbTree::Empty); rewrite(er_right, RbTree::Node(ec_id, ec_parent, ec_color, ec_left, ec_right));
                                                unfold(erase_outcome(RbTree::Node(erased, erased_parent, erased_color, RbTree::Node(el_id, el_parent, el_color, el_left, el_right), RbTree::Node(er_id, er_parent, er_color, RbTree::Empty, RbTree::Node(ec_id, ec_parent, ec_color, ec_left, ec_right))), old(up.model)));
                                                normalize();
                                            }
                                            have erase_splice(old(tree.model)) == rb_erase_immediate_child_model(old(tree.model)) by {
                                                rewrite(old(tree.model), RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right));
                                                rewrite(erased_left, RbTree::Node(el_id, el_parent, el_color, el_left, el_right));
                                                rewrite(erased_right, RbTree::Node(er_id, er_parent, er_color, er_left, er_right));
                                                rewrite(er_left, RbTree::Empty); rewrite(er_right, RbTree::Node(ec_id, ec_parent, ec_color, ec_left, ec_right));
                                                unfold(erase_splice(RbTree::Node(erased, erased_parent, erased_color, RbTree::Node(el_id, el_parent, el_color, el_left, el_right), RbTree::Node(er_id, er_parent, er_color, RbTree::Empty, RbTree::Node(ec_id, ec_parent, ec_color, ec_left, ec_right)))));
                                                normalize();
                                            }
                                            have is_rb(RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right)) == 1 by {
                                                rewrite(RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right), tree.model); close();
                                            }
                                            have ctx_rb(up.model, black_height(RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right)),
                                                rb_color(RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right))) == 1 by {
                                                rewrite(RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right), tree.model); close();
                                            }
                                            apply(ctx_consistent_node_children(up.model, erased, erased_parent, erased_color, erased_left, erased_right, 0));
                                            apply(rb_node_is_reflexive(erased_parent));
                                            apply(rb_parent_consistent_node(erased, erased_parent, erased_color, erased_left, erased_right, erased_parent));
                                            apply(erase_context_parent(up.model, erased, erased_parent, erased_color, erased_left, erased_right));
                                            have ctx_rb(up.model, black_height(RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right)), erased_color)
                                                == ctx_rb(up.model, black_height(RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right)),
                                                    rb_color(RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right))) by {
                                                unfold(rb_color(RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right))); normalize();
                                            }
                                            let { left: l, right: r } = unfold(tree);
                                            let old_left = fold(erase_saved_left(node), { child: node->rb_left });
                                            apply(rb_parent_is_node_parent(er_id, er_parent, er_color, er_left, er_right, erased));
                                            have is_rb(RbTree::Node(erased, erased_parent, erased_color, erased_left,
                                                RbTree::Node(er_id, erased, er_color, RbTree::Empty, er_right))) == 1 by {
                                                rewrite(erased, er_parent);
                                                rewrite(RbTree::Empty, er_left);
                                                rewrite(RbTree::Node(er_id, er_parent, er_color, er_left, er_right), erased_right);
                                                rewrite(er_parent, erased); close();
                                            }
                                            have rb_parent_consistent(RbTree::Node(erased, erased_parent, erased_color, erased_left,
                                                RbTree::Node(er_id, erased, er_color, RbTree::Empty, er_right)), erased_parent) == 1 by {
                                                rewrite(erased, er_parent); rewrite(RbTree::Empty, er_left);
                                                rewrite(RbTree::Node(er_id, er_parent, er_color, er_left, er_right), erased_right);
                                                rewrite(er_parent, erased); close();
                                            }
                                            have ctx_rb(up.model, black_height(RbTree::Node(erased, erased_parent, erased_color, erased_left,
                                                RbTree::Node(er_id, erased, er_color, RbTree::Empty, er_right))), erased_color) == 1 by {
                                                rewrite(erased, er_parent); rewrite(RbTree::Empty, er_left);
                                                rewrite(RbTree::Node(er_id, er_parent, er_color, er_left, er_right), erased_right);
                                                rewrite(er_parent, erased); close();
                                            }
                                            apply(rb_erase_immediate_successor_child(erased, er_id, erased_parent, erased_color, erased_left, er_color, er_right, up.model));
                                            apply(ctx_consistent_swap(up.model, erased, erased_parent, erased_color, erased_left, erased_right,
                                                rb_immediate_successor_child(er_id, erased_parent, erased_color, erased_left, er_right), 0));
                                            apply(plug_parent_consistent_transport(up.model, rb_immediate_successor_child(er_id, erased_parent, erased_color, erased_left, er_right), 0));
                                            have rb_tree_parent_consistent(plug(old(up.model), rb_immediate_successor_child(er_id, erased_parent, erased_color, erased_left, er_right))) == 1 by {
                                                unfold(rb_tree_parent_consistent(plug(old(up.model), rb_immediate_successor_child(er_id, erased_parent, erased_color, erased_left, er_right))));
                                            }
                                            have is_rb_root(plug(old(up.model), rb_immediate_successor_child(er_id, erased_parent, erased_color, erased_left, er_right))) == 1 by {
                                                rewrite(old(up.model), up.model); close();
                                            }
                                            have rb_erase_immediate_child_model(old(tree.model)) == rb_immediate_successor_child(er_id, erased_parent, erased_color, erased_left, er_right) by {
                                                rewrite(old(tree.model), RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right));
                                                rewrite(erased_right, RbTree::Node(er_id, er_parent, er_color, er_left, er_right));
                                                unfold(rb_erase_immediate_child_model(RbTree::Node(erased, erased_parent, erased_color, erased_left, RbTree::Node(er_id, er_parent, er_color, er_left, er_right))));
                                                normalize();
                                            }
                                            have rb_inorder(erase_splice(old(tree.model))) == list::append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model)))) by {
                                                rewrite(erase_splice(old(tree.model)), rb_erase_immediate_child_model(old(tree.model)));
                                                rewrite(rb_erase_immediate_child_model(old(tree.model)), rb_immediate_successor_child(er_id, erased_parent, erased_color, erased_left, er_right));
                                                rewrite(rb_left(old(tree.model)), erased_left); rewrite(rb_right(old(tree.model)), erased_right);
                                                rewrite(erased_right, RbTree::Node(er_id, er_parent, er_color, er_left, er_right));
                                                rewrite(er_left, RbTree::Empty); rewrite(er_parent, erased); close();
                                            }
                                            have rb_immediate_successor_child(er_id, erased_parent, erased_color, erased_left, er_right)
                                                == RbTree::Node(er_id, erased_parent, erased_color, RbTree::Node(el_id, er_id, el_color, el_left, el_right), RbTree::Node(ec_id, er_id, Color::Black, ec_left, ec_right)) by {
                                                unfold(rb_immediate_successor_child(er_id, erased_parent, erased_color, erased_left, er_right));
                                                rewrite(erased_left, RbTree::Node(el_id, el_parent, el_color, el_left, el_right));
                                                rewrite(er_right, RbTree::Node(ec_id, ec_parent, ec_color, ec_left, ec_right));
                                                unfold(rb_reparent(RbTree::Node(el_id, el_parent, el_color, el_left, el_right), er_id));
                                                unfold(rb_recolor(RbTree::Node(ec_id, ec_parent, ec_color, ec_left, ec_right), Color::Black));
                                                unfold(rb_reparent(RbTree::Node(ec_id, ec_parent, Color::Black, ec_left, ec_right), er_id));
                                                normalize();
                                            }
                                            let { left: sleft, right: sright } = unfold(r);
                                            unfold(sleft);
                                            let { left: lleft, right: lright } = unfold(l);
                                            have (old(node->__rb_parent_color) & 1) == color_bit(erased_color) by {
                                                rewrite(old(node->__rb_parent_color), node->__rb_parent_color); close();
                                            }
                                            have old(node->__rb_parent_color) == address(erased_parent) + (old(node->__rb_parent_color) & 1) by {
                                                rewrite(old(node->__rb_parent_color), node->__rb_parent_color); close();
                                            }
                                            let erased_tag = fold(erase_saved_parent(node, erased_parent), { word: node->__rb_parent_color, color: erased_color });
                                            let left_color = fold(erase_saved_color(el_id), { color: el_color });
                                            mark before_left_splice;
                                            let left_children = fold(erase_saved_children(el_id), { left: el_id->rb_left, right: el_id->rb_right });
                                            with(erase_callbacks(augment)) { step_until(assignment(tmp, 5).entry); }
                                            unfold(old_left);
                                            have node->rb_left == el_id by close();
                                            step(); step();
                                            unfold(left_color);
                                            mark before_left_reparent;
                                            have (tmp->__rb_parent_color & 1) == color_bit(el_color) by close();
                                            step();
                                            have at(before_left_reparent, successor->rb_left) == el_id by close();
                                            have contains(memory(el_id->__rb_parent_color), region(43).footprint) by close();
                                            have separate(memory(el_id->__rb_parent_color), memory(successor->rb_left)) by close();
                                            apply(click::separation::contains_refl(memory(successor->rb_left)));
                                            apply(click::separation::separate_restrict(memory(el_id->__rb_parent_color), memory(successor->rb_left), region(43).footprint, memory(successor->rb_left)));
                                            have successor->rb_left == at(before_left_reparent, successor->rb_left) by {
                                                preserve(memory(successor->rb_left), region(43));
                                            }
                                            have successor->rb_left == el_id by close();
                                            let successor_links = fold(erase_saved_children(successor), { left: el_id, right: successor->rb_right });
                                            have aligned(successor, 8) by close();
                                            have ((tmp->__rb_parent_color & ~3) as (struct rb_node *)) == successor by {
                                                close() using {
                                                    aligned(successor, 8);
                                                    aligned(successor, 8) implies ((tmp->__rb_parent_color & ~3) as (struct rb_node *)) == successor;
                                                };
                                            }
                                            apply(packed_parent_word(successor, at(before_left_reparent, tmp->__rb_parent_color)));
                                            have tmp->__rb_parent_color == address(successor) + (tmp->__rb_parent_color & 1) by {
                                                rewrite(tmp->__rb_parent_color, ((at(before_left_reparent, tmp->__rb_parent_color) & 1) | address(successor)));
                                                close();
                                            }
                                            have (tmp->__rb_parent_color & 1) == color_bit(el_color) by {
                                                rewrite(tmp->__rb_parent_color, ((at(before_left_reparent, tmp->__rb_parent_color) & 1) | address(successor)));
                                                rewrite(((at(before_left_reparent, tmp->__rb_parent_color) & 1) | address(successor)) & 1,
                                                    at(before_left_reparent, tmp->__rb_parent_color) & 1);
                                                close();
                                            }
                                            let moved_parent = fold(erase_saved_parent(tmp, successor), {
                                                word: tmp->__rb_parent_color, color: el_color
                                            });
                                            unfold(left_children);
                                            unfold(moved_parent);
                                            have tmp->rb_left == at(before_left_splice, el_id->rb_left) by close();
                                            have tmp->rb_right == at(before_left_splice, el_id->rb_right) by close();
                                            let moved_left = fold(rb_at(tmp), {
                                                model: RbTree::Node(el_id, successor, el_color, el_left, el_right),
                                                left: lleft, right: lright
                                            });
                                            have rb_parent_is(RbTree::Node(el_id, er_id, el_color, el_left, el_right), er_id) == 1 by {
                                                unfold(rb_parent_is(RbTree::Node(el_id, er_id, el_color, el_left, el_right), er_id)); normalize();
                                            }
                                            unfold(erased_tag);
                                            have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == erased_parent by close();
                                            step_until(call(__rb_change_child, 2).entry);
                                            have tmp == erased_parent;
                                            mark transplant;
                                            have ctx_node_is(up.model, tmp) == 1;
                                            let { links: incoming, frame: outer_frame } = detach_erase_links(node, tmp, root, { before: up });
                                            observe(erase_callbacks(augment));
                                            mark incoming_link_state;
                                            let { sibling_ptr: sibling_ptr, root_count: root_count, parent_count: parent_count, tag: parent_tag, above: above } = unfold(incoming);
                                            have separate(memory(root[0..root_count]), memory(*augment)) by close();
                                            have separate(memory(tmp[0..parent_count]), memory(*augment)) by close();
                                            let incoming = fold(erase_change_links(node, tmp, root), {
                                                model: at(incoming_link_state, incoming.model), sibling_ptr: sibling_ptr,
                                                root_count: root_count, parent_count: parent_count, tag: parent_tag, above: above
                                            });
                                            let { updated: linked } = step(__rb_change_child, { links: incoming });
                                            have linked.model == outer_frame.model;
                                            have linked.sibling_ptr == outer_frame.sibling_ptr;
                                            have linked.tag == outer_frame.tag;
                                            have linked.above == outer_frame.above;
                                            let { updated: remaining } = attach_erase_links(successor, tmp, root, { links: linked, frame: outer_frame });
                                            have successor == er_id by close();
                                            let { left: cleft, right: cright } = unfold(sright);
                                            have child2 == ec_id by close();
                                            step(); step();
                                            have child2->__rb_parent_color == (address(successor) | 1) by close();
                                            have aligned(successor, 8) by close();
                                            have ((child2->__rb_parent_color & ~3) as (struct rb_node *)) == er_id by { rewrite(er_id, successor); close(); }
                                            have (child2->__rb_parent_color & 1) == color_bit(Color::Black) by {
                                                rewrite(child2->__rb_parent_color, (address(successor) | 1));
                                                unfold(color_bit(Color::Black));
                                            }
                                            apply(click::integer::uint64_or_commute(address(successor), 1u64));
                                            apply(packed_parent_word(successor, 1u64));
                                            have (1u64 | address(successor)) == address(successor) + 1u64 by close();
                                            have (child2->__rb_parent_color & 1) == 1 by close();
                                            have child2->__rb_parent_color == address(er_id) + (child2->__rb_parent_color & 1) by {
                                                rewrite((child2->__rb_parent_color & 1), 1);
                                                rewrite(er_id, successor);
                                                rewrite(child2->__rb_parent_color, (address(successor) | 1));
                                                rewrite((address(successor) | 1), (1u64 | address(successor)));
                                                close();
                                            }
                                            let moved_right = fold(rb_at(child2), { model: RbTree::Node(ec_id, er_id, Color::Black, ec_left, ec_right), left: cleft, right: cright });
                                            step_until(statement(4).statement(5).statement(15).entry);
                                            mark before_copying_tag;
                                            have ((pc & ~3) as (struct rb_node *)) == erased_parent by close();
                                            step();
                                            have successor->__rb_parent_color == at(before_copying_tag, pc) by close();
                                            have ((successor->__rb_parent_color & ~3) as (struct rb_node *)) == erased_parent by close();
                                            let replacement_tag = fold(erase_saved_parent(successor, erased_parent), { word: at(before_copying_tag, pc), color: erased_color });
                                            step_until(statement(5).entry);
                                            unfold(successor_links);
                                            unfold(replacement_tag);
                                            have tmp == er_id by close();
                                            have tmp->rb_left == el_id by close();
                                            have tmp->rb_right == ec_id by close();
                                            have ((tmp->__rb_parent_color & ~3) as (struct rb_node *)) == erased_parent by close();
                                            have rb_parent_is(RbTree::Node(ec_id, er_id, Color::Black, ec_left, ec_right), er_id) == 1 by {
                                                unfold(rb_parent_is(RbTree::Node(ec_id, er_id, Color::Black, ec_left, ec_right), er_id)); normalize();
                                            }
                                            let replacement = fold(rb_at(tmp), {
                                                model: RbTree::Node(tmp, erased_parent, erased_color, RbTree::Node(el_id, er_id, el_color, el_left, el_right), RbTree::Node(ec_id, er_id, Color::Black, ec_left, ec_right)),
                                                left: moved_left, right: moved_right
                                            });
                                            have rb_tree_parent_consistent(plug(remaining.model, replacement.model)) == 1 by {
                                                rewrite(remaining.model, old(up.model));
                                                rewrite(replacement.model, RbTree::Node(er_id, erased_parent, erased_color, RbTree::Node(el_id, er_id, el_color, el_left, el_right), RbTree::Node(ec_id, er_id, Color::Black, ec_left, ec_right)));
                                                rewrite(RbTree::Node(er_id, erased_parent, erased_color, RbTree::Node(el_id, er_id, el_color, el_left, el_right), RbTree::Node(ec_id, er_id, Color::Black, ec_left, ec_right)), rb_immediate_successor_child(er_id, erased_parent, erased_color, erased_left, er_right));
                                                close();
                                            }
                                            mark balanced;
                                            let { whole: whole } = refold_to_root(er_id, root, { c: remaining, t: replacement });
                                            have whole.model == plug(old(up.model), rb_erase_immediate_child_model(old(tree.model))) by {
                                                rewrite(whole.model, plug(at(balanced, remaining.model), RbTree::Node(er_id, erased_parent, erased_color, RbTree::Node(el_id, er_id, el_color, el_left, el_right), RbTree::Node(ec_id, er_id, Color::Black, ec_left, ec_right))));
                                                rewrite(at(balanced, remaining.model), old(up.model));
                                                rewrite(rb_erase_immediate_child_model(old(tree.model)), rb_immediate_successor_child(er_id, erased_parent, erased_color, erased_left, er_right));
                                                rewrite(rb_immediate_successor_child(er_id, erased_parent, erased_color, erased_left, er_right), RbTree::Node(er_id, erased_parent, erased_color, RbTree::Node(el_id, er_id, el_color, el_left, el_right), RbTree::Node(ec_id, er_id, Color::Black, ec_left, ec_right)));
                                                normalize();
                                            }
                                            with(erase_callbacks(augment)) { step_until(function.exit); }
                                            let out = fold(erase_out(root, result), { model: EraseOutcome::Balanced(plug(old(up.model), rb_erase_immediate_child_model(old(tree.model)))), whole: whole });
                                            have erase_out_rb(out.model) == 1 by {
                                                rewrite(out.model, EraseOutcome::Balanced(plug(old(up.model), rb_erase_immediate_child_model(old(tree.model)))));
                                                unfold(erase_out_rb(EraseOutcome::Balanced(plug(old(up.model), rb_erase_immediate_child_model(old(tree.model))))));
                                                rewrite(rb_erase_immediate_child_model(old(tree.model)), rb_immediate_successor_child(er_id, erased_parent, erased_color, erased_left, er_right));
                                                close();
                                            }
                                            have rb_tree_parent_consistent(erase_out_tree(out.model)) == 1 by {
                                                rewrite(out.model, EraseOutcome::Balanced(plug(old(up.model), rb_erase_immediate_child_model(old(tree.model)))));
                                                unfold(erase_out_tree(EraseOutcome::Balanced(plug(old(up.model), rb_erase_immediate_child_model(old(tree.model))))));
                                                rewrite(rb_erase_immediate_child_model(old(tree.model)), rb_immediate_successor_child(er_id, erased_parent, erased_color, erased_left, er_right));
                                                close();
                                            }
                                            have erase_out_tree(out.model) == plug(old(up.model), rb_erase_immediate_child_model(old(tree.model))) by {
                                                rewrite(out.model, EraseOutcome::Balanced(plug(old(up.model), rb_erase_immediate_child_model(old(tree.model)))));
                                                unfold(erase_out_tree(EraseOutcome::Balanced(plug(old(up.model), rb_erase_immediate_child_model(old(tree.model)))))); normalize();
                                            }
                                            have out.model == erase_outcome(old(tree.model), old(up.model)) by {
                                                rewrite(out.model, EraseOutcome::Balanced(plug(old(up.model), rb_erase_immediate_child_model(old(tree.model)))));
                                                rewrite(erase_outcome(old(tree.model), old(up.model)), EraseOutcome::Balanced(plug(old(up.model), rb_erase_immediate_child_model(old(tree.model)))));
                                                normalize();
                                            }
                                            have rb_tree_parent_consistent(erase_out_tree(out.model)) == 1 by {
                                                rewrite(out.model, EraseOutcome::Balanced(plug(old(up.model), rb_erase_immediate_child_model(old(tree.model)))));
                                                unfold(erase_out_tree(EraseOutcome::Balanced(plug(old(up.model), rb_erase_immediate_child_model(old(tree.model))))));
                                                rewrite(rb_erase_immediate_child_model(old(tree.model)), rb_immediate_successor_child(er_id, erased_parent, erased_color, erased_left, er_right));
                                                close();
                                            }
                                            have erase_out_tree(out.model) == plug(old(up.model), erase_splice(old(tree.model))) by {
                                                rewrite(out.model, EraseOutcome::Balanced(plug(old(up.model), rb_erase_immediate_child_model(old(tree.model)))));
                                                unfold(erase_out_tree(EraseOutcome::Balanced(plug(old(up.model), rb_erase_immediate_child_model(old(tree.model))))));
                                                rewrite(erase_splice(old(tree.model)), rb_erase_immediate_child_model(old(tree.model)));
                                                normalize();
                                            }
                                            close();
                                        },
                                    }
                                },
                                RbTree::Node(ep_id, ep_parent, ep_color, ep_left, ep_right) => {
                                    // The deeper-successor shape was handled first.
                                    have rb_left(tree.model) == erased_left;
                                    have rb_right(tree.model) == erased_right;
                                    have erased_left != RbTree::Empty;
                                    have erased_right != RbTree::Empty;
                                    have rb_left(tree.model) != RbTree::Empty by { rewrite(rb_left(tree.model), erased_left); close(); }
                                    have rb_right(tree.model) != RbTree::Empty by { rewrite(rb_right(tree.model), erased_right); close(); }
                                    have rb_left(erased_right) == er_left by {
                                        rewrite(erased_right, RbTree::Node(er_id, er_parent, er_color, er_left, er_right));
                                        unfold(rb_left(RbTree::Node(er_id, er_parent, er_color, er_left, er_right))); normalize();
                                    }
                                    have er_left != RbTree::Empty;
                                    have rb_left(rb_right(tree.model)) != RbTree::Empty by {
                                        rewrite(rb_right(tree.model), erased_right); rewrite(rb_left(erased_right), er_left); close();
                                    }
                                    have rb_left(tree.model) != RbTree::Empty and rb_right(tree.model) != RbTree::Empty
                                        and rb_left(rb_right(tree.model)) != RbTree::Empty by close();
                                    contradiction(rb_left(tree.model) != RbTree::Empty and rb_right(tree.model) != RbTree::Empty
                                        and rb_left(rb_right(tree.model)) != RbTree::Empty);
                                },
                            }
                        },
                    }
                },
            }
        },
    }
    }
}
