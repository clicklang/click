# Explicit pointer framing exhausts the simple-tactic budget in the non-root splice

## Violated invariant

A written `transport ... using` must complete or refuse locally with work bounded
by its explicit proof and the affected memory history. The non-root deeper
successor prototype exhausts the 750,000-unit simple-tactic budget at statement
62 while framing the unchanged `child->rb_right` field. It supplies ten explicit
separation/alias premises. Establishing the read immediately after the parent-link
call avoids this particular failure, but is not a performance fix for the written
transport.

Reproduced on `9fddface6b88799fbdd8ba840d7da3a382a7497d`, including the pending
field-proposition ABI-width correction. That correction fixes a separate reduced
framing failure; the budget exhaustion remains. The C extraction is unchanged.

The incomplete profile reports `explicit fact transport: quantified frame` open
310,334 units into the interrupted invocation when the enclosing tactic reaches
750,001 units. Completed attribution includes composition-owned store separation
and general pointer distinctness. This identifies the frontier, not a root-cause
conclusion. Do not increase the budget or expand surrounding smart tactics.

## Reproduction

From the repository root, materialize the frozen proof below and verify it:

```sh
python3 - <<'PY_REPRO'
from pathlib import Path
source = Path('bugs/rbtree-pointer-transport-simple-budget.md').read_text()
proof = source.split('```click\n', 1)[1].split('\n```', 1)[0]
target = Path('/tmp/rbtree-budget-repro')
(target / 'rbtree-erase').mkdir(parents=True, exist_ok=True)
for name in ['rbtree-model', 'rbtree-insert']:
    link = target / name
    if not link.exists():
        link.symlink_to(Path.cwd() / 'examples' / name, target_is_directory=True)
(target / 'rbtree-erase/rb_erase_augmented.c').write_bytes(
    Path('examples/rbtree-erase/rb_erase_augmented.c').read_bytes())
(target / 'rbtree-erase/transport-budget.click').write_text(proof)
PY_REPRO
click verify /tmp/rbtree-budget-repro/rbtree-erase/transport-budget.click
click profile /tmp/rbtree-budget-repro/rbtree-erase/transport-budget.click
```

The large proof is retained to make the observation reproducible while reduction
continues. The intended small regression should retain a modeled sibling pointer,
write the other fields through aliases, call a named-context parent-link helper,
and request its saved pointer equality after rejoining the outer context. Include
an overwritten-link negative and grow unrelated resource facts independently.

## Acceptance criteria

- Reduce the repeated framing/distinctness work and add a deterministic scaling
  regression. Ordinary `verify` must return a checked result or a local proof
  refusal for this exact source without exhausting a simple-tactic budget.
- Preserve full pointer identities, read widths, and call/store history. Reject
  an actually overwritten link; do not add an assumption that grants the goal.
- Retest the non-root splice frontier, then resume the example. Remove this file
  after the fix and its regressions land.

## Frozen proof

```click
// Root deletion with a deeper black-leaf successor. The result identifies
// the nonnull parent at which erase-color repair must begin.
verifying "rb_erase_augmented.c";

import "../rbtree-model/rbtree_spine_resources.click";

theorem erase_context_parent(ctx: Context, node: struct rb_node*, parent: struct rb_node*,
    color: Color, left: RbTree, right: RbTree) {
    requires ctx_consistent(ctx, RbTree::Node(node, parent, color, left, right), 0) == 1;
    ensures ctx_node_is(ctx, parent) == 1 by {
        induct(ctx) as ih {
            Context::Top => {
                apply(ctx_consistent_top(RbTree::Node(node, parent, color, left, right), 0));
                apply(rb_parent_consistent_node_fixes_parent(node, parent, color, left, right, 0));
                unfold(ctx_node_is(Context::Top, parent));
                normalize() using { parent == 0; };
            }
            Context::Left(id, gp, c, sibling, up) => {
                apply(ctx_consistent_left_focus(id, gp, c, sibling, up, RbTree::Node(node, parent, color, left, right), 0));
                apply(rb_parent_consistent_node_fixes_parent(node, parent, color, left, right, id));
                unfold(ctx_node_is(Context::Left(id, gp, c, sibling, up), parent));
                normalize() using { parent == id; };
            }
            Context::Right(id, gp, c, sibling, up) => {
                apply(ctx_consistent_right_focus(id, gp, c, sibling, up, RbTree::Node(node, parent, color, left, right), 0));
                apply(rb_parent_consistent_node_fixes_parent(node, parent, color, left, right, id));
                unfold(ctx_node_is(Context::Right(id, gp, c, sibling, up), parent));
                normalize() using { parent == id; };
            }
        }
    }
    ensures ctx == ctx_reroot(ctx, parent) by {
        induct(ctx) as ih {
            Context::Top => {
                apply(ctx_consistent_top(RbTree::Node(node, parent, color, left, right), 0));
                apply(rb_parent_consistent_node_fixes_parent(node, parent, color, left, right, 0));
                unfold(ctx_reroot(Context::Top, parent));
                normalize();
            }
            Context::Left(id, gp, c, sibling, up) => {
                apply(ctx_consistent_left_focus(id, gp, c, sibling, up, RbTree::Node(node, parent, color, left, right), 0));
                apply(rb_parent_consistent_node_fixes_parent(node, parent, color, left, right, id));
                unfold(ctx_reroot(Context::Left(id, gp, c, sibling, up), parent));
                rewrite(parent == id); normalize();
            }
            Context::Right(id, gp, c, sibling, up) => {
                apply(ctx_consistent_right_focus(id, gp, c, sibling, up, RbTree::Node(node, parent, color, left, right), 0));
                apply(rb_parent_consistent_node_fixes_parent(node, parent, color, left, right, id));
                unfold(ctx_reroot(Context::Right(id, gp, c, sibling, up), parent));
                rewrite(parent == id); normalize();
            }
        }
    }
    ensures rb_parent_consistent(RbTree::Node(node, parent, color, left, right), parent) == 1 by {
        apply(ctx_consistent_node_children(ctx, node, parent, color, left, right, 0));
        have parent == parent by { normalize(); }
        apply(rb_node_is_equal(parent, parent));
        apply(rb_parent_consistent_node(node, parent, color, left, right, parent));
        assumption();
    }
}

function erase_deep_context(tree: RbTree, up: Context) -> Context {
    match tree {
        RbTree::Empty => up,
        RbTree::Node(node, parent, color, left, right) => rb_successor_context(erase_minimum_identity(rb_minimum(right)), parent, color, left, right, up),
    }
}

function erase_deep_model(tree: RbTree) -> RbTree {
    match tree {
        RbTree::Empty => RbTree::Empty,
        RbTree::Node(node, parent, color, left, right) => rb_successor_splice(erase_minimum_identity(rb_minimum(right)), parent, color, left, right),
    }
}

void __rb_change_child(struct rb_node* old, struct rb_node* new,
                       struct rb_node* parent, struct rb_root* root) {
    consumes before: ctx_at(old, root);
    owns old->__rb_parent_color;
    requires old != 0;
    requires ctx_node_is(before.model, parent) == 1;
    produces after: ctx_at(new, root);
    ensures after.model == old(before.model);
    ensures old->__rb_parent_color == old(old->__rb_parent_color);
} by {
    have old != 0 by { assumption(); }
    match before.model {
        Context::Top => {
            have parent == 0 by {
                have ctx_node_is(Context::Top, parent) == 1 by {
                    rewrite(Context::Top == before.model); assumption();
                }
                if parent == 0 { assumption(); } else {
                    have ctx_node_is(Context::Top, parent) != 1 by {
                        unfold(ctx_node_is(Context::Top, parent)); normalize() using { not(parent == 0); };
                    }
                    contradiction(ctx_node_is(Context::Top, parent) == 1);
                }
            }
            unfold(before);
            execute();
            let after = fold(ctx_at(new, root), { model: Context::Top });
            simp();
        },
        Context::Left(identity, grandparent, color, sibling_model, outer_model) => {
            have parent == identity by {
                have ctx_node_is(Context::Left(identity, grandparent, color, sibling_model, outer_model), parent) == 1 by {
                    rewrite(Context::Left(identity, grandparent, color, sibling_model, outer_model) == before.model); assumption();
                }
                if parent == identity { assumption(); } else {
                    have ctx_node_is(Context::Left(identity, grandparent, color, sibling_model, outer_model), parent) != 1 by {
                        unfold(ctx_node_is(Context::Left(identity, grandparent, color, sibling_model, outer_model), parent)); normalize() using { not(parent == identity); };
                    }
                    contradiction(ctx_node_is(Context::Left(identity, grandparent, color, sibling_model, outer_model), parent) == 1);
                }
            }
            let { sibling: sibling, up: outer } = unfold(before);
            execute();
            let after = fold(ctx_at(new, root), {
                model: Context::Left(identity, grandparent, color, sibling_model, outer_model)
            }, { sibling: sibling, up: outer });
            simp();
        },
        Context::Right(identity, grandparent, color, sibling_model, outer_model) => {
            have parent == identity by {
                have ctx_node_is(Context::Right(identity, grandparent, color, sibling_model, outer_model), parent) == 1 by {
                    rewrite(Context::Right(identity, grandparent, color, sibling_model, outer_model) == before.model); assumption();
                }
                if parent == identity { assumption(); } else {
                    have ctx_node_is(Context::Right(identity, grandparent, color, sibling_model, outer_model), parent) != 1 by {
                        unfold(ctx_node_is(Context::Right(identity, grandparent, color, sibling_model, outer_model), parent)); normalize() using { not(parent == identity); };
                    }
                    contradiction(ctx_node_is(Context::Right(identity, grandparent, color, sibling_model, outer_model), parent) == 1);
                }
            }
            let { sibling: sibling, up: outer } = unfold(before);
            match sibling.model {
                RbTree::Empty => {
                    unfold(sibling);
                    have identity->rb_left == 0 by { simp(); }
                    have parent->rb_left == 0 by { simp(); }
                    have old != 0 by { assumption(); }
                    have parent->rb_left != old by {
                        if parent->rb_left == old {
                            have old == 0 by { normalize() using { parent->rb_left == old; parent->rb_left == 0; } }
                            contradiction(old != 0);
                        } else { assumption(); }
                    }
                    execute();
                    let sibling = fold(rb_at(parent->rb_left), { model: RbTree::Empty });
                    let after = fold(ctx_at(new, root), {
                        model: Context::Right(identity, grandparent, color, sibling_model, outer_model)
                    }, { sibling: sibling, up: outer });
                    simp();
                },
                RbTree::Node(sid, sp, sc, sl, sr) => {
                    let { left: left, right: right } = unfold(sibling);
                    execute();
                    let sibling = fold(rb_at(parent->rb_left), {
                        model: RbTree::Node(sid, sp, sc, sl, sr)
                    }, { left: left, right: right });
                    let after = fold(ctx_at(new, root), {
                        model: Context::Right(identity, grandparent, color, sibling_model, outer_model)
                    }, { sibling: sibling, up: outer });
                    simp();
                },
            }
        },
    }
}

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
                rewrite(c.model == EraseSpine::Top);
                unfold(erase_spine_parent(EraseSpine::Top, anchor)); normalize();
            }
            have parent == anchor by { normalize() using { } }
            unfold(c);
            have parent != 0 by { simp(); }
            let frame = fold(erase_spine_frame(parent, anchor), { model: EraseSpine::Top });
            have parent->rb_left == focus by { simp(); }
            have frame.model == old(c.model) by { simp(); }
        },
        EraseSpine::Left(identity, grandparent, color, sibling_model, up_model) => {
            have erase_spine_parent(c.model, anchor) == identity by {
                rewrite(c.model == EraseSpine::Left(identity, grandparent, color, sibling_model, up_model));
                unfold(erase_spine_parent(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model), anchor)); normalize();
            }
            have parent == identity by { normalize() using { } }
            let { sibling: sibling, up: up } = unfold(c);
            have parent != 0 by { simp(); }
            let frame = fold(erase_spine_frame(parent, anchor), {
                model: EraseSpine::Left(identity, grandparent, color, sibling_model, up_model)
            }, { sibling: sibling, up: up });
            have parent->rb_left == focus by { simp(); }
            have frame.model == old(c.model) by { simp(); }
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
            have anchor->rb_left == focus by { simp(); }
            let c = fold(erase_spine_at(focus, anchor), { model: EraseSpine::Top });
            have c.model == old(frame.model) by { simp(); }
        },
        EraseSpine::Left(identity, grandparent, color, sibling_model, up_model) => {
            let { sibling: sibling, up: up } = unfold(frame);
            have parent != 0 by { rewrite(parent == identity); assumption(); }
            have aligned(parent, 8) by { rewrite(parent == identity); assumption(); }
            have rb_parent_is(sibling_model, parent) == 1 by { rewrite(parent == identity); assumption(); }
            let c = fold(erase_spine_at(focus, anchor), {
                model: EraseSpine::Left(identity, grandparent, color, sibling_model, up_model)
            }, { sibling: sibling, up: up });
            have c.model == old(frame.model) by { simp(); }
        },
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
        rewrite(old(base.model) == EraseAnchorFrame::At(ap, ac, ar, au));
        unfold(erase_anchor_context(anchor, EraseAnchorFrame::At(ap, ac, ar, au))); normalize();
    }
    match c.model {
        EraseSpine::Top => {
            unfold(c);
            let { right: right, up: outer_context } = unfold(base);
            let context = fold(ctx_at(focus, root), {
                model: Context::Left(anchor, ap, ac, ar, au)
            }, { sibling: right, up: outer_context });
            have context.model == ctx_concat(erase_context(old(c.model)),
                Context::Left(anchor, ap, ac, ar, au)) by {
                rewrite(old(c.model) == EraseSpine::Top);
                unfold(erase_context(EraseSpine::Top));
                unfold(ctx_concat(Context::Top, Context::Left(anchor, ap, ac, ar, au)));
                simp();
            }
            have context.model == ctx_concat(erase_context(old(c.model)), erase_anchor_context(anchor, old(base.model))) by {
                rewrite(erase_anchor_context(anchor, old(base.model)) == Context::Left(anchor, ap, ac, ar, au)); assumption();
            }
        },
        EraseSpine::Left(identity, grandparent, color, sibling_model, up_model) => {
            have erase_spine_links(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model), anchor) == 1 by {
                rewrite(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model) == old(c.model)); assumption();
            }
            unfold(erase_spine_links(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model), anchor));
            have grandparent == erase_spine_parent(up_model, anchor) by {
                if grandparent == erase_spine_parent(up_model, anchor) { assumption(); } else {
                    have erase_spine_links(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model), anchor) != 1 by {
                        unfold(erase_spine_links(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model), anchor));
                        normalize() using { not(grandparent == erase_spine_parent(up_model, anchor)); }
                    }
                    contradiction(erase_spine_links(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model), anchor) == 1);
                }
            }
            have erase_spine_links(up_model, anchor) == 1 by {
                have erase_spine_links(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model), anchor) == erase_spine_links(up_model, anchor) by {
                    unfold(erase_spine_links(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model), anchor));
                    normalize() using { grandparent == erase_spine_parent(up_model, anchor); }
                }
                rewrite(erase_spine_links(up_model, anchor) == erase_spine_links(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model), anchor)); assumption();
            }
            let { sibling: sibling, up: path_tail } = unfold(c);
            apply(erase_spine_depth_is_nonnegative(up_model));
            have 0 <= erase_spine_depth(path_tail.model) by { rewrite(path_tail.model == up_model); assumption(); }
            have erase_spine_depth(old(c.model)) == erase_spine_depth(up_model) + 1 by {
                rewrite(old(c.model) == EraseSpine::Left(identity, grandparent, color, sibling_model, up_model));
                unfold(erase_spine_depth(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model))); normalize();
            }
            have erase_spine_depth(path_tail.model) < erase_spine_depth(old(c.model)) by {
                rewrite(path_tail.model == up_model);
                arithmetic() using { erase_spine_depth(old(c.model)) == erase_spine_depth(up_model) + 1; }
            }
            have path_tail.model == up_model by { simp(); }
            mark grafting_tail;
            let { context: above } = graft_erase_spine(identity, anchor, root, { c: path_tail, base: base });
            have above.model == ctx_concat(erase_context(at(grafting_tail, path_tail.model)),
                erase_anchor_context(anchor, at(grafting_tail, base.model))) by { assumption(); }
            have at(grafting_tail, base.model) == EraseAnchorFrame::At(ap, ac, ar, au) by { assumption(); }
            have at(grafting_tail, path_tail.model) == up_model by { simp(); }
            have erase_anchor_context(anchor, EraseAnchorFrame::At(ap, ac, ar, au)) == Context::Left(anchor, ap, ac, ar, au) by {
                unfold(erase_anchor_context(anchor, EraseAnchorFrame::At(ap, ac, ar, au))); normalize();
            }
            have above.model == ctx_concat(erase_context(up_model),
                Context::Left(anchor, ap, ac, ar, au)) by {
                rewrite(up_model == at(grafting_tail, path_tail.model));
                rewrite(Context::Left(anchor, ap, ac, ar, au) == erase_anchor_context(anchor, EraseAnchorFrame::At(ap, ac, ar, au)));
                rewrite(EraseAnchorFrame::At(ap, ac, ar, au) == at(grafting_tail, base.model)); assumption();
            }
            apply(erase_spine_context_parent(up_model, anchor, ap, ac, ar, au));
            have ctx_node_is(above.model, grandparent) == 1 by {
                rewrite(above.model == ctx_concat(erase_context(up_model),
                    Context::Left(anchor, ap, ac, ar, au)));
                rewrite(grandparent == erase_spine_parent(up_model, anchor)); assumption();
            }
            have above.model == ctx_reroot(above.model, grandparent) by {
                rewrite(above.model == ctx_concat(erase_context(up_model),
                    Context::Left(anchor, ap, ac, ar, au)));
                rewrite(grandparent == erase_spine_parent(up_model, anchor)); assumption();
            }
            let context = fold(ctx_at(focus, root), {
                model: Context::Left(identity, grandparent, color, sibling_model,
                    ctx_concat(erase_context(up_model), Context::Left(anchor, ap, ac, ar, au)))
            }, { sibling: sibling, up: above });
            have context.model == ctx_concat(erase_context(old(c.model)),
                Context::Left(anchor, ap, ac, ar, au)) by {
                rewrite(old(c.model) == EraseSpine::Left(identity, grandparent, color, sibling_model, up_model));
                unfold(erase_context(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model)));
                unfold(ctx_concat(Context::Left(identity, grandparent, color, sibling_model, erase_context(up_model)),
                    Context::Left(anchor, ap, ac, ar, au)));
                simp();
            }
            have context.model == ctx_concat(erase_context(old(c.model)), erase_anchor_context(anchor, old(base.model))) by {
                rewrite(erase_anchor_context(anchor, old(base.model)) == Context::Left(anchor, ap, ac, ar, au)); assumption();
            }
        },
    }
        },
    }
}

struct rb_node* __rb_erase_augmented(struct rb_node* node, struct rb_root* root,
    const struct rb_augment_callbacks* augment) {
    consumes tree: rb_at(node);
    consumes up: ctx_at(node, root);
    requires up.model != Context::Top;
    requires tree.model != RbTree::Empty;
    requires rb_left(tree.model) != RbTree::Empty;
    requires rb_right(tree.model) != RbTree::Empty;
    requires rb_left(rb_right(tree.model)) != RbTree::Empty;
    requires erase_minimum_child(rb_minimum(rb_right(tree.model))) == RbTree::Empty;
    requires erase_minimum_color(rb_minimum(rb_right(tree.model))) == Color::Black;
    requires ctx_consistent(up.model, tree.model, 0) == 1;
    requires ctx_rb(up.model, black_height(tree.model), rb_color(tree.model)) == 1;
    requires is_rb(tree.model) == 1;
    owns erase_callbacks(augment);
    produces node->__rb_parent_color;
    produces node->rb_left;
    produces node->rb_right;
    produces hole: rb_at(0);
    produces deficit: ctx_at(0, root);
    ensures hole.model == RbTree::Empty;
    ensures deficit.model == erase_deep_context(old(tree.model), old(up.model));
    ensures ctx_rb(deficit.model, Nat::Succ(Nat::Zero), Color::Black) == 1;
    ensures ctx_consistent(deficit.model, hole.model, 0) == 1;
    ensures plug(deficit.model, hole.model) == plug(old(up.model), erase_deep_model(old(tree.model)));
    ensures result == rb_min_parent(rb_right(old(tree.model)));
    ensures result != 0;
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
            have erase_minimum_child(rb_minimum(right_model)) == RbTree::Empty by {
                rewrite(right_model == rb_right(tree.model)); assumption();
            }
            have erase_minimum_color(rb_minimum(right_model)) == Color::Black by {
                rewrite(right_model == rb_right(tree.model)); assumption();
            }
            have rb_left(right_model) != RbTree::Empty by { rewrite(right_model == rb_right(tree.model)); assumption(); }
            have ctx_consistent(up.model, RbTree::Node(identity, parent_model, color, left_model, right_model), 0) == 1 by {
                rewrite(RbTree::Node(identity, parent_model, color, left_model, right_model) == tree.model); assumption();
            }
            apply(erase_context_parent(up.model, identity, parent_model, color, left_model, right_model));
            apply(ctx_consistent_node_children(up.model, identity, parent_model, color, left_model, right_model, 0));
            have is_rb(RbTree::Node(identity, parent_model, color, left_model, right_model)) == 1 by {
                rewrite(RbTree::Node(identity, parent_model, color, left_model, right_model) == tree.model); assumption();
            }
            have ctx_rb(up.model, black_height(RbTree::Node(identity, parent_model, color, left_model, right_model)), rb_color(RbTree::Node(identity, parent_model, color, left_model, right_model))) == 1 by {
                rewrite(RbTree::Node(identity, parent_model, color, left_model, right_model) == tree.model); assumption();
            }
            have rb_left(old(tree.model)) == left_model by { simp(); }
            have rb_right(old(tree.model)) == right_model by { simp(); }
            let { left: l, right: r } = unfold(tree);
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
                            have rb_parent_consistent(RbTree::Node(rid, rp, rc, rl, rr), identity) == 1 by {
                                rewrite(RbTree::Node(rid, rp, rc, rl, rr) == right_model); assumption();
                            }
                            apply(rb_parent_consistent_node_left(rid, rp, rc, rl, rr, identity));
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
                                        unfold(plug(old(up.model), t.model)); simp();
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
                                                RbTree::Empty => { unfold(t); have tmp != 0 by { simp(); } contradiction(tmp == 0); },
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
                                    have tmp == 0 by { simp(); }
                                    match t.model {
                                        RbTree::Node(a, b, col, lt, rt) => {
                                            have t.model == RbTree::Empty by { assumption(); }
                                            have t.model != RbTree::Empty by { rewrite(t.model == RbTree::Node(a, b, col, lt, rt)); normalize(); }
                                            contradiction(t.model == RbTree::Empty);
                                        },
                                        RbTree::Empty => {
                                            have c.model != EraseSpine::Top by { normalize(); }
                                            match c.model {
                                                EraseSpine::Top => { contradiction(c.model == EraseSpine::Top); },
                                                EraseSpine::Left(mid, mp, mc, mr, mu) => {
                                                    have plug(erase_context(c.model), t.model) == plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr)) by {
                                                        rewrite(c.model == EraseSpine::Left(mid, mp, mc, mr, mu));
                                                        unfold(erase_context(EraseSpine::Left(mid, mp, mc, mr, mu)));
                                                        unfold(plug(Context::Left(mid, mp, mc, mr, erase_context(mu)), t.model));
                                                        rewrite(t.model == RbTree::Empty); normalize();
                                                    }
                                                    have plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr)) == rl by {
                                                        rewrite(plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr)) == plug(erase_context(c.model), t.model)); assumption();
                                                    }
                                                    have RbTree::Node(mid, mp, mc, RbTree::Empty, mr) != RbTree::Empty by { normalize(); }
                                                    apply(erase_spine_minimum(mu, RbTree::Node(mid, mp, mc, RbTree::Empty, mr)));
                                                    have rb_minimum(rl) == RbMinimum::Found(mid, mc, mr) by {
                                                        rewrite(rl == plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr)));
                                                        rewrite(rb_minimum(plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr)))
                                                            == rb_minimum(RbTree::Node(mid, mp, mc, RbTree::Empty, mr)));
                                                        unfold(rb_minimum(RbTree::Node(mid, mp, mc, RbTree::Empty, mr))); normalize();
                                                    }
                                                    apply(rb_minimum_nonempty_left(rid, rp, rc, rl, rr));
                                                    have rb_minimum(right_model) == RbMinimum::Found(mid, mc, mr) by {
                                                        rewrite(right_model == RbTree::Node(rid, rp, rc, rl, rr));
                                                        rewrite(rb_minimum(RbTree::Node(rid, rp, rc, rl, rr)) == rb_minimum(rl)); assumption();
                                                    }
                                                    have erase_minimum_child(rb_minimum(right_model)) == mr by {
                                                        rewrite(rb_minimum(right_model) == RbMinimum::Found(mid, mc, mr));
                                                        unfold(erase_minimum_child(RbMinimum::Found(mid, mc, mr))); normalize();
                                                    }
                                                    have erase_minimum_color(rb_minimum(right_model)) == mc by {
                                                        rewrite(rb_minimum(right_model) == RbMinimum::Found(mid, mc, mr));
                                                        unfold(erase_minimum_color(RbMinimum::Found(mid, mc, mr))); normalize();
                                                    }
                                                    have mr == RbTree::Empty by { rewrite(mr == erase_minimum_child(rb_minimum(right_model))); assumption(); }
                                                    have mc == Color::Black by { rewrite(mc == erase_minimum_color(rb_minimum(right_model))); assumption(); }
                                                    have rb_minimum(right_model) == RbMinimum::Found(mid, Color::Black, RbTree::Empty) by {
                                                        rewrite(Color::Black == mc); rewrite(RbTree::Empty == mr); assumption();
                                                    }
                                                    apply(rb_erase_black_successor_splice(identity, mid, parent_model, color, left_model, right_model, up.model, 0));
                                                    have erase_minimum_identity(rb_minimum(right_model)) == mid by {
                                                        rewrite(rb_minimum(right_model) == RbMinimum::Found(mid, mc, mr));
                                                        unfold(erase_minimum_identity(RbMinimum::Found(mid, mc, mr))); normalize();
                                                    }
                                                    have rb_parent_consistent(plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr)), rid) == 1 by {
                                                        rewrite(plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr)) == rl); assumption();
                                                    }
                                                    apply(erase_spine_focus_parent_consistent(mu, RbTree::Node(mid, mp, mc, RbTree::Empty, mr), rid));
                                                    apply(erase_parent_consistent_parent_is(RbTree::Node(mid, mp, mc, RbTree::Empty, mr), erase_spine_parent(mu, rid)));
                                                    apply(rb_parent_is_node_parent(mid, mp, mc, RbTree::Empty, mr, erase_spine_parent(mu, rid)));
                                                    apply(erase_spine_links_from_tree(mu, RbTree::Node(mid, mp, mc, RbTree::Empty, mr), rid));
                                                    apply(erase_spine_min_parent(mu, RbTree::Node(mid, mp, mc, RbTree::Empty, mr)));
                                                    apply(rb_min_parent_nonempty_left(rid, rp, rc, rl, rr));
                                                    have rb_min_parent(right_model) == mp by {
                                                        rewrite(right_model == RbTree::Node(rid, rp, rc, rl, rr));
                                                        rewrite(rb_min_parent(RbTree::Node(rid, rp, rc, rl, rr)) == rb_min_parent(rl));
                                                        rewrite(rl == plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr)));
                                                        rewrite(rb_min_parent(plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr)))
                                                            == rb_min_parent(RbTree::Node(mid, mp, mc, RbTree::Empty, mr)));
                                                        unfold(rb_min_parent(RbTree::Node(mid, mp, mc, RbTree::Empty, mr))); normalize();
                                                    }
                                                    let { sibling: min_right, up: path } = unfold(c);
                                                    have (mid->__rb_parent_color & 1) == color_bit(mc) by { assumption(); }
                                                    unfold(t);
                                                    have parent == erase_spine_parent(path.model, child) by { simp(); }
                                                    have parent == mp by {
                                                        rewrite(parent == erase_spine_parent(path.model, child));
                                                        rewrite(path.model == mu); rewrite(child == rid);
                                                        rewrite(erase_spine_parent(mu, rid) == mp); normalize();
                                                    }
                                                    have path.model == mu by { simp(); }
                                                    mark opened_spine;
                                                    let { frame: link_frame } = open_erase_spine_link(successor, parent, child, { c: path });
                                                    have link_frame.model == at(opened_spine, path.model) by { assumption(); }
                                                    have link_frame.model == mu by { simp(); }
                                                    step(); step(); step(); step();
                                                    have node->rb_left == lid by { simp(); }
                                                    unfold(erase_callbacks(augment));
                                                    have min_right.model == RbTree::Empty by { rewrite(min_right.model == mr); assumption(); }
                                                    unfold(min_right);
                                                    have color_bit(mc) == 1 by { rewrite(mc == Color::Black); unfold(color_bit(Color::Black)); normalize(); }
                                                    have (successor->__rb_parent_color & 1) == 1 by { simp(); }
                                                    execute_until(statement(54));
                                                    have separate(memory(child->rb_right), memory(mid->__rb_parent_color)) by { simp(); }
                                                    have separate(memory(child->rb_right), memory(mid->rb_right)) by { simp(); }
                                                    have separate(memory(child->rb_right), memory(lid->__rb_parent_color)) by { simp(); }
                                                    have separate(memory(child->rb_right), memory(node->__rb_parent_color)) by { simp(); }
                                                    have separate(memory(child->rb_right), memory(parent->rb_left)) by { simp(); }
                                                    have separate(memory(child->rb_right), memory(mid->rb_left)) by { simp(); }
                                                    have separate(memory(child->rb_right), memory(child->__rb_parent_color)) by { simp(); }
                                                    let moved_left = fold(rb_at(lid), {
                                                        model: RbTree::Node(lid, mid, lc, ll, lr)
                                                    }, { left: ll_tree, right: lr_tree });
                                                    have moved_left.model == rb_reparent(left_model, mid) by {
                                                        rewrite(left_model == RbTree::Node(lid, lp, lc, ll, lr));
                                                        unfold(rb_reparent(RbTree::Node(lid, lp, lc, ll, lr), mid)); normalize();
                                                    }
                                                    have tmp == parent_model by { simp(); }
                                                    have ctx_node_is(up.model, tmp) == 1 by {
                                                        rewrite(tmp == parent_model); assumption();
                                                    }
                                                    have (successor->__rb_parent_color & 1) == 1 by { simp(); }
                                                    have parent->rb_left == 0 by { simp(); }
                                                    mark transplant;
                                                    let { after: root_context } = step(__rb_change_child(node, successor, tmp, root), { before: up });
                                                    have parent->rb_left == at(transplant, parent->rb_left) by { normalize(); }
                                                    have node->rb_left == lid by { simp(); }
                                                    have parent->rb_left == 0 by { simp(); }
                                                    have root_context.model == at(transplant, up.model) by { assumption(); }
                                                    have root_context.model == old(up.model) by { simp(); }
                                                    have mid->__rb_parent_color == at(transplant, mid->__rb_parent_color) by { simp(); }
                                                    have (mid->__rb_parent_color & 1) == 1 by { simp(); }
                                                    have successor == mid by { simp(); }
                                                    have (successor->__rb_parent_color & 1) == 1 by {
                                                        rewrite(successor == mid); assumption();
                                                    }
                                                    execute_until(statement(62));
                                                    let hole = fold(rb_at(0), { model: RbTree::Empty });
                                                    have parent->rb_left == 0 by { simp(); }
                                                    mark closing_spine;
                                                    let { c: path2 } = close_erase_spine_link(0, parent, child, { frame: link_frame });
                                                    have path2.model == at(closing_spine, link_frame.model) by { assumption(); }
                                                    have path2.model == mu by { simp(); }
                                                    apply(rb_reparent_parent_is(left_model, mid));
                                                    have rb_parent_is(rb_reparent(left_model, mid), mid) == 1 by { assumption(); }
                                                    have mid->rb_left == lid by { simp(); }
                                                    have mid->rb_right == child by { simp(); }
                                                    let above = fold(ctx_at(child, root), {
                                                        model: Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model))
                                                    }, { sibling: moved_left, up: root_context });
                                                    have ctx_node_is(above.model, mid) == 1 by {
                                                        rewrite(above.model == Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)));
                                                        unfold(ctx_node_is(Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)), mid)); normalize();
                                                    }
                                                    have above.model == ctx_reroot(above.model, mid) by {
                                                        rewrite(above.model == Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)));
                                                        unfold(ctx_reroot(Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)), mid)); normalize();
                                                    }
                                                    have child == rid by { simp(); }
                                                    have tmp == mid by { simp(); }
                                                    have child->rb_right == at(transplant, child->rb_right) by {
                                                        transport(at(transplant, child->rb_right) == at(transplant, child->rb_right), child->rb_right == at(transplant, child->rb_right)) using {
                                                            separate(memory(child->rb_right), memory(mid->__rb_parent_color));
                                                            separate(memory(child->rb_right), memory(mid->rb_right));
                                                            separate(memory(child->rb_right), memory(mid->rb_left));
                                                            separate(memory(child->rb_right), memory(child->__rb_parent_color));
                                                            tmp == mid;
                                                            child == rid;
                                                            at(transplant, node->rb_left) == lid;
                                                            separate(memory(child->rb_right), memory(lid->__rb_parent_color));
                                                            separate(memory(child->rb_right), memory(node->__rb_parent_color));
                                                            separate(memory(child->rb_right), memory(parent->rb_left));
                                                        };
                                                    }
                                                    have right_sibling.model == rr by { simp(); }
                                                    let anchor_frame = fold(erase_anchor_frame(child, root), {
                                                        model: EraseAnchorFrame::At(mid, rc, rr, Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)))
                                                    }, { right: right_sibling, up: above });
                                                    have erase_spine_links(path2.model, child) == 1 by {
                                                        rewrite(path2.model == mu); rewrite(child == rid); assumption();
                                                    }
                                                    mark grafting;
                                                    let { context: deficit } = graft_erase_spine(0, child, root, { c: path2, base: anchor_frame });
                                                    have deficit.model == ctx_concat(erase_context(at(grafting, path2.model)),
                                                        erase_anchor_context(child, EraseAnchorFrame::At(mid, rc, rr, Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model))))) by { assumption(); }
                                                    have at(grafting, path2.model) == mu by { assumption(); }
                                                    have erase_anchor_context(child, EraseAnchorFrame::At(mid, rc, rr,
                                                        Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model))))
                                                        == Context::Left(rid, mid, rc, rr, Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model))) by {
                                                        unfold(erase_anchor_context(child, EraseAnchorFrame::At(mid, rc, rr,
                                                            Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)))));
                                                        rewrite(child == rid); normalize();
                                                    }
                                                    have deficit.model == ctx_concat(erase_context(mu),
                                                        Context::Left(rid, mid, rc, rr, Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)))) by {
                                                        rewrite(mu == at(grafting, path2.model));
                                                        rewrite(Context::Left(rid, mid, rc, rr, Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)))
                                                            == erase_anchor_context(child, EraseAnchorFrame::At(mid, rc, rr,
                                                                Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)))));
                                                        assumption();
                                                    }
                                                    apply(erase_spine_min_context(mu, RbTree::Node(mid, mp, mc, RbTree::Empty, mr),
                                                        Context::Left(rid, mid, rc, rr, Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)))));
                                                    apply(rb_min_context_nonempty_left(rid, mid, rc, rl, rr,
                                                        Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model))));
                                                    have rb_successor_context(mid, parent_model, color, left_model, right_model, old(up.model))
                                                        == ctx_concat(erase_context(mu), Context::Left(rid, mid, rc, rr,
                                                            Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)))) by {
                                                        unfold(rb_successor_context(mid, parent_model, color, left_model, right_model, old(up.model)));
                                                        rewrite(right_model == RbTree::Node(rid, rp, rc, rl, rr));
                                                        unfold(rb_reparent(RbTree::Node(rid, rp, rc, rl, rr), mid));
                                                        rewrite(rb_min_context(RbTree::Node(rid, mid, rc, rl, rr),
                                                            Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)))
                                                            == rb_min_context(rl, Context::Left(rid, mid, rc, rr,
                                                                Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)))));
                                                        rewrite(rl == plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr)));
                                                        rewrite(rb_min_context(plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr)),
                                                            Context::Left(rid, mid, rc, rr, Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model))))
                                                            == rb_min_context(RbTree::Node(mid, mp, mc, RbTree::Empty, mr),
                                                                ctx_concat(erase_context(mu), Context::Left(rid, mid, rc, rr, Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model))))));
                                                        unfold(rb_min_context(RbTree::Node(mid, mp, mc, RbTree::Empty, mr),
                                                            ctx_concat(erase_context(mu), Context::Left(rid, mid, rc, rr, Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)))))); normalize();
                                                    }
                                                    have deficit.model == rb_successor_context(mid, parent_model, color, left_model, right_model, old(up.model)) by {
                                                        rewrite(rb_successor_context(mid, parent_model, color, left_model, right_model, old(up.model))
                                                            == ctx_concat(erase_context(mu), Context::Left(rid, mid, rc, rr,
                                                                Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model))))); assumption();
                                                    }
                                                    have deficit.model == erase_deep_context(old(tree.model), old(up.model)) by {
                                                        rewrite(old(tree.model) == RbTree::Node(identity, parent_model, color, left_model, right_model));
                                                        unfold(erase_deep_context(RbTree::Node(identity, parent_model, color, left_model, right_model), old(up.model)));
                                                        rewrite(erase_minimum_identity(rb_minimum(right_model)) == mid); assumption();
                                                    }
                                                    have ctx_rb(deficit.model, Nat::Succ(Nat::Zero), Color::Black) == 1 by {
                                                        rewrite(deficit.model == rb_successor_context(mid, parent_model, color, left_model, right_model, old(up.model))); assumption();
                                                    }
                                                    have ctx_consistent(deficit.model, hole.model, 0) == 1 by {
                                                        rewrite(hole.model == RbTree::Empty);
                                                        rewrite(deficit.model == rb_successor_context(mid, parent_model, color, left_model, right_model, old(up.model))); assumption();
                                                    }
                                                    have plug(deficit.model, hole.model) == plug(old(up.model), erase_deep_model(old(tree.model))) by {
                                                        rewrite(hole.model == RbTree::Empty);
                                                        rewrite(old(tree.model) == RbTree::Node(identity, parent_model, color, left_model, right_model));
                                                        unfold(erase_deep_model(RbTree::Node(identity, parent_model, color, left_model, right_model)));
                                                        rewrite(erase_minimum_identity(rb_minimum(right_model)) == mid);
                                                        rewrite(deficit.model == rb_successor_context(mid, parent_model, color, left_model, right_model, old(up.model))); assumption();
                                                    }
                                                    have rebalance == rb_min_parent(rb_right(old(tree.model))) by {
                                                        rewrite(rb_right(old(tree.model)) == right_model);
                                                        rewrite(rb_min_parent(right_model) == mp); simp();
                                                    }
                                                    have rebalance != 0 by { simp(); }
                                                    execute(); fold(erase_callbacks(augment)); simp();
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
