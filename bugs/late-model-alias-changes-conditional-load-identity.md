# A later model alias changes the spelling of a C conditional load

## Violated invariant

After a model match exposes another spelling of an owned pointer, a source
condition synthesized from a checked C successor must still select that
successor. In the deeper rbtree successor proof, execution retains one
`uint64` load variable while lowering the suggested condition names another
load at the same snapshot through the newly exposed pointer alias. A proof
split on that source condition therefore leaves both C successors feasible.

The executor progress guard now refuses this case promptly. Without that
guard, `execute()` repeatedly splits the same condition until stack overflow.
The guard fixes the crash, but the source condition still cannot select the
C operation it was synthesized from.

## Reproduction

Reproduced on `fc297b473` with the executor progress guard and shared opaque
alias read coordinates. Save the following as
`examples/rbtree-erase/late_alias_repro.click`, then run:

```sh
click verify examples/rbtree-erase/late_alias_repro.click
```

It refuses the `execute()` in the empty replacement-child arm, at the pinned
C's `rebalance = rb_is_black(successor) ? parent : NULL`. The diagnostic is
`execute cannot advance after selecting this path condition`. Replacing that
call with `execute_until(statement(58)); step();` exposes two successors and
suggests splitting on `(successor->__rb_parent_color & 1u64) == 0u64`; that
split does not resolve the checked successor. The C is unchanged. The trivial
postcondition intentionally isolates execution; this is not an erase proof.
Remove the temporary sidecar after reproducing so example-directory checks
do not select this unfinished contract.

```click
verifying "rb_erase_augmented.c";

import "../rbtree-model/rbtree_resources.click";
import "../rbtree-model/rbtree_erase_child.click";

spec enum EraseSpine {
    Top,
    Left(struct rb_node*, struct rb_node*, Color, RbTree, EraseSpine),
}

function erase_context(spine: EraseSpine) -> Context decreases spine {
    match spine {
        EraseSpine::Top => Context::Top,
        EraseSpine::Left(identity, grandparent, color, sibling, up) =>
            Context::Left(identity, grandparent, color, sibling, erase_context(up)),
    }
}

# The path ends at anchor->rb_left, leaving anchor's other fields available.
resource erase_spine_at(focus: struct rb_node*, anchor: struct rb_node*) {
    field model: EraseSpine;
    match model {
        EraseSpine::Top => {
            owns anchor->rb_left;
            fact anchor != 0;
            fact anchor->rb_left == focus;
        },
        EraseSpine::Left(identity, grandparent, color, sibling_model, up_model) => {
            owns identity->__rb_parent_color;
            owns identity->rb_left;
            owns identity->rb_right;
            owns sibling: rb_at(identity->rb_right);
            owns up: erase_spine_at(identity, anchor);
            fact identity != 0;
            fact aligned(identity, 8);
            fact aligned(grandparent, 8);
            fact identity->rb_left == focus;
            fact identity->__rb_parent_color
                == address(grandparent) + (identity->__rb_parent_color & 1);
            fact (identity->__rb_parent_color & 1) == color_bit(color);
            fact sibling.model == sibling_model;
            fact up.model == up_model;
            fact rb_parent_is(sibling_model, identity) == 1;
        },
    }
}

function erase_spine_parent(spine: EraseSpine, anchor: struct rb_node*) -> struct rb_node* {
    match spine {
        EraseSpine::Top => anchor,
        EraseSpine::Left(identity, grandparent, color, sibling, up) => identity,
    }
}

contract void AugmentRotate(struct rb_node* old, struct rb_node* new) {
    requires new != 0;
    ensures 1 == 1;
}

contract void ErasePropagate(struct rb_node* node, struct rb_node* stop) {
    ensures 1 == 1;
}

contract void EraseCopy(struct rb_node* node, struct rb_node* successor) {
    requires node != 0;
    requires successor != 0;
    ensures 1 == 1;
}

resource erase_callbacks(augment: const struct rb_augment_callbacks*) {
    owns augment->propagate;
    owns augment->copy;
    owns augment->rotate;
    fact ErasePropagate(augment->propagate);
    fact EraseCopy(augment->copy);
    fact AugmentRotate(augment->rotate);
}

struct rb_node* __rb_erase_augmented(struct rb_node* node, struct rb_root* root,
                                    const struct rb_augment_callbacks* augment) {
    consumes tree: rb_at(node);
    consumes up: ctx_at(node, root);
    requires up.model == Context::Top;
    requires tree.model != RbTree::Empty;
    requires rb_parent_is(tree.model, 0) == 1;
    requires rb_color(tree.model) == Color::Black;
    requires rb_left(tree.model) != RbTree::Empty;
    requires rb_right(tree.model) != RbTree::Empty;
    requires rb_left(rb_right(tree.model)) != RbTree::Empty;
    owns erase_callbacks(augment);
    ensures 1 == 1;
} by {
    match tree.model {
        RbTree::Empty => { contradiction(tree.model == RbTree::Empty); },
        RbTree::Node(identity, parent_model, color, left_model, right_model) => {
            have rb_left(tree.model) == left_model by {
                rewrite(tree.model == RbTree::Node(identity, parent_model, color, left_model, right_model));
                unfold(rb_left(RbTree::Node(identity, parent_model, color, left_model, right_model))); normalize();
            }
            have rb_right(tree.model) == right_model by {
                rewrite(tree.model == RbTree::Node(identity, parent_model, color, left_model, right_model));
                unfold(rb_right(RbTree::Node(identity, parent_model, color, left_model, right_model))); normalize();
            }
            have left_model != RbTree::Empty by { rewrite(left_model == rb_left(tree.model)); assumption(); }
            have right_model != RbTree::Empty by { rewrite(right_model == rb_right(tree.model)); assumption(); }
            have rb_left(right_model) != RbTree::Empty by { rewrite(right_model == rb_right(tree.model)); assumption(); }
            have rb_parent_is(RbTree::Node(identity, parent_model, color, left_model, right_model), 0) == 1 by {
                rewrite(RbTree::Node(identity, parent_model, color, left_model, right_model) == tree.model); assumption();
            }
            apply(rb_parent_is_node_parent(identity, parent_model, color, left_model, right_model, 0));
            have color == Color::Black by {
                unfold(rb_color(RbTree::Node(identity, parent_model, color, left_model, right_model)));
                rewrite(color == rb_color(RbTree::Node(identity, parent_model, color, left_model, right_model)));
                rewrite(RbTree::Node(identity, parent_model, color, left_model, right_model) == tree.model); assumption();
            }
            unfold(up);
            let { left: l, right: r } = unfold(tree);
            have color_bit(Color::Black) == 1 by { unfold(color_bit(Color::Black)); normalize(); }
            have (node->__rb_parent_color & 1) == 1 by {
                rewrite((node->__rb_parent_color & 1) == color_bit(color));
                rewrite(color == Color::Black); unfold(color_bit(Color::Black)); normalize();
            }
            have node->__rb_parent_color == 1 by { simp(); }
            match left_model {
                RbTree::Empty => { contradiction(left_model == RbTree::Empty); },
                RbTree::Node(lid, lp, lc, ll, lr) => {
                    let { left: ll_tree, right: lr_tree } = unfold(l);
                    match right_model {
                        RbTree::Empty => { contradiction(right_model == RbTree::Empty); },
                        RbTree::Node(rid, rp, rc, rl, rr) => {
                            have rl != RbTree::Empty by {
                                unfold(rb_left(RbTree::Node(rid, rp, rc, rl, rr)));
                                rewrite(rl == rb_left(RbTree::Node(rid, rp, rc, rl, rr)));
                                rewrite(RbTree::Node(rid, rp, rc, rl, rr) == right_model); assumption();
                            }
                            let { left: t, right: right_sibling } = unfold(r);
                            match rl {
                                RbTree::Empty => { contradiction(rl == RbTree::Empty); },
                                RbTree::Node(iid, ip, ic, il, ir) => {
                            let { left: init_l, right: init_r } = unfold(t);
                            let t = fold(rb_at(iid), { model: RbTree::Node(iid, ip, ic, il, ir) }, { left: init_l, right: init_r });
                            step(); step(); step(); step(); step(); step(); step(); step(); step(); step(); step(); step(); step(); step();
                            let c = fold(erase_spine_at(tmp, child), { model: EraseSpine::Top });
                            have plug(erase_context(c.model), t.model) == rl by {
                                rewrite(c.model == EraseSpine::Top);
                                unfold(erase_context(EraseSpine::Top));
                                unfold(plug(Context::Top, t.model)); simp();
                            }
                            have successor == erase_spine_parent(c.model, child) by {
                                rewrite(c.model == EraseSpine::Top);
                                unfold(erase_spine_parent(EraseSpine::Top, child)); simp();
                            }
                            loop {
                                owns c: erase_spine_at(tmp, child);
                                owns t: rb_at(tmp);
                                decreases t;
                                invariant tmp != 0;
                                invariant successor == erase_spine_parent(c.model, child);
                                invariant plug(erase_context(c.model), t.model) == rl;
                                initialize by simp;
                                preserve by {
                                    match t.model {
                                        RbTree::Empty => { unfold(t); contradiction(tmp == 0); },
                                        RbTree::Node(tid, tp, tc, tl, tr) => {
                                            have plug(erase_context(EraseSpine::Left(tid, tp, tc, tr, c.model)), tl) == rl by {
                                                unfold(erase_context(EraseSpine::Left(tid, tp, tc, tr, c.model)));
                                                unfold(plug(Context::Left(tid, tp, tc, tr, erase_context(c.model)), tl));
                                                rewrite(RbTree::Node(tid, tp, tc, tl, tr) == t.model); assumption();
                                            }
                                            let { left: next, right: sibling } = unfold(t);
                                            have tmp == tid by { assumption(); }
                                            have tid != 0 by { rewrite(tid == tmp); assumption(); }
                                            have erase_spine_parent(EraseSpine::Left(tid, tp, tc, tr, c.model), child) == tid by {
                                                unfold(erase_spine_parent(EraseSpine::Left(tid, tp, tc, tr, c.model), child)); normalize();
                                            }
                                            let frame = fold(erase_spine_at(tmp->rb_left, child),
                                                { model: EraseSpine::Left(tid, tp, tc, tr, c.model) }, { sibling: sibling, up: c });
                                            step(); step(); step();
                                            have successor == erase_spine_parent(frame.model, child) by { simp(); }
                                            if tmp == 0 {
                                            } else {
                                                close_invariants();
                                            }
                                        },
                                    }
                                }
                            }
                            have node->rb_left == lid by { simp(); }
                            have c.model != EraseSpine::Top by { normalize(); }
                            match c.model {
                                EraseSpine::Top => { contradiction(c.model == EraseSpine::Top); },
                                EraseSpine::Left(mid, mp, mc, mr, mu) => {
                                    let { sibling: min_right, up: path } = unfold(c);
                                    unfold(t);
                                    have parent == erase_spine_parent(path.model, child) by { simp(); }
                                    match path.model {
                                        EraseSpine::Top => {
                                            have erase_spine_parent(path.model, child) == child by {
                                                rewrite(path.model == EraseSpine::Top);
                                                unfold(erase_spine_parent(EraseSpine::Top, child)); normalize();
                                            }
                                            have parent == child by { simp(); }
                                            unfold(path);
                                            step(); step(); step(); step();
                                            have node->rb_left == lid by { simp(); }
                                            unfold(erase_callbacks(augment));
                                            match min_right.model {
                                                RbTree::Empty => { unfold(min_right); execute(); },
                                                RbTree::Node(cid, cp, cc, cl, cr) => {
                                                    let { left: child_left, right: child_right } = unfold(min_right);
                                                    execute();
                                                },
                                            }
                                        },
                                        EraseSpine::Left(pid, pp, parent_color, ps, pu) => {
                                            have erase_spine_parent(path.model, child) == pid by {
                                                rewrite(path.model == EraseSpine::Left(pid, pp, parent_color, ps, pu));
                                                unfold(erase_spine_parent(EraseSpine::Left(pid, pp, parent_color, ps, pu), child)); normalize();
                                            }
                                            have parent == pid by { simp(); }
                                            let { sibling: parent_right, up: above } = unfold(path);
                                            step(); step(); step(); step();
                                            have node->rb_left == lid by { simp(); }
                                            unfold(erase_callbacks(augment));
                                            match min_right.model {
                                                RbTree::Empty => { unfold(min_right); execute(); },
                                                RbTree::Node(cid, cp, cc, cl, cr) => {
                                                    let { left: child_left, right: child_right } = unfold(min_right);
                                                    execute();
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
        },
    }
}
```

## Intended smaller regression and acceptance

Reduce this to a materialized `uint64` read, followed by a checked pointer
alias with a symbolic offset, then a masked conditional read through the same
C variable. Check both truth values and both directions of the alias. Keep
negative cases for absent equality, a different field offset, and a write
that changes the observed value.

The suggested explicit split and the corresponding simple C step must agree;
ordinary verification and expansion must agree too. Retain the executor's
repeated-condition refusal as a separate crash regression. Address lookup
must use indexed facts, with deterministic scaling checks if its representation
changes; do not fix this by scanning unrelated aliases or by editing the pinned
C. Finish the deeper successor proof only after the tooling regression passes.
