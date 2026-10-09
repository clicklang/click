// Exact left-only path from a deeper successor to the original right child.
import "rbtree_erase_child.click";
import "rbtree_resources.click";

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

function erase_spine_depth(ctx: EraseSpine) -> Integer
    decreases ctx
{
    match ctx {
        EraseSpine::Top => 0,
        EraseSpine::Left(identity, grandparent, color, sibling_model, up_model) =>
            erase_spine_depth(up_model) + 1,
    }
}

theorem erase_spine_depth_is_nonnegative(ctx: EraseSpine) {
    ensures 0 <= erase_spine_depth(ctx) by {
        induct(ctx) as ih {
            EraseSpine::Top => {
                unfold(erase_spine_depth(EraseSpine::Top));
                normalize();
            }
            EraseSpine::Left(identity, grandparent, color, sibling_model, up_model) => {
                apply(ih(up_model));
                unfold(erase_spine_depth(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model)));
                arithmetic() using { 0 <= erase_spine_depth(up_model); }
            }
        }
    }
}

theorem erase_parent_consistent_parent_is(t: RbTree, p: struct rb_node*) {
    requires rb_parent_consistent(t, p) == 1;
    ensures rb_parent_is(t, p) == 1 by {
        induct(t) as ih {
            RbTree::Empty => {
                unfold(rb_parent_is(RbTree::Empty, p));
                normalize();
            }
            RbTree::Node(node, parent, color, left, right) => {
                apply(rb_parent_consistent_node_parent(node, parent, color, left, right, p));
                apply(rb_parent_is_node_is(node, parent, color, left, right, p));
                rewrite(rb_parent_is(RbTree::Node(node, parent, color, left, right), p)
                    == rb_node_is(parent, p));
                assumption();
            }
        }
    }
}

theorem erase_spine_minimum(spine: EraseSpine, tree: RbTree) {
    requires tree != RbTree::Empty;
    ensures rb_minimum(plug(erase_context(spine), tree)) == rb_minimum(tree) by {
        induct(spine) as ih {
            EraseSpine::Top => {
                unfold(erase_context(EraseSpine::Top));
                unfold(plug(Context::Top, tree)); normalize();
            }
            EraseSpine::Left(identity, parent, color, sibling, up) => {
                have RbTree::Node(identity, parent, color, tree, sibling) != RbTree::Empty by { normalize(); }
                apply(ih(up, RbTree::Node(identity, parent, color, tree, sibling)));
                apply(rb_minimum_nonempty_left(identity, parent, color, tree, sibling));
                unfold(erase_context(EraseSpine::Left(identity, parent, color, sibling, up)));
                unfold(plug(Context::Left(identity, parent, color, sibling, erase_context(up)), tree));
                rewrite(rb_minimum(plug(erase_context(up), RbTree::Node(identity, parent, color, tree, sibling)))
                    == rb_minimum(RbTree::Node(identity, parent, color, tree, sibling)));
                assumption();
            }
        }
    }
}

# Cutting the minimum below a left-only spine leaves its ancestor frames intact.

theorem erase_spine_remove_min_blackened(spine: EraseSpine, tree: RbTree) {
    requires tree != RbTree::Empty;
    ensures rb_remove_min_blackened(plug(erase_context(spine), tree))
        == plug(erase_context(spine), rb_remove_min_blackened(tree)) by {
        induct(spine) as ih {
            EraseSpine::Top => {
                unfold(erase_context(EraseSpine::Top));
                unfold(plug(Context::Top, tree));
                unfold(plug(Context::Top, rb_remove_min_blackened(tree))); normalize();
            }
            EraseSpine::Left(identity, parent, color, sibling, up) => {
                have RbTree::Node(identity, parent, color, tree, sibling) != RbTree::Empty by { normalize(); }
                apply(ih(up, RbTree::Node(identity, parent, color, tree, sibling)));
                apply(rb_remove_min_blackened_nonempty_left(identity, parent, color, tree, sibling));
                unfold(erase_context(EraseSpine::Left(identity, parent, color, sibling, up)));
                unfold(plug(Context::Left(identity, parent, color, sibling, erase_context(up)), tree));
                unfold(plug(Context::Left(identity, parent, color, sibling, erase_context(up)), rb_remove_min_blackened(tree)));
                rewrite(rb_remove_min_blackened(plug(erase_context(up), RbTree::Node(identity, parent, color, tree, sibling)))
                    == plug(erase_context(up), rb_remove_min_blackened(RbTree::Node(identity, parent, color, tree, sibling))));
                rewrite(rb_remove_min_blackened(RbTree::Node(identity, parent, color, tree, sibling))
                    == RbTree::Node(identity, parent, color, rb_remove_min_blackened(tree), sibling));
                normalize();
            }
        }
    }
}

function erase_spine_parent(spine: EraseSpine, anchor: struct rb_node*) -> struct rb_node* {
    match spine {
        EraseSpine::Top => anchor,
        EraseSpine::Left(identity, grandparent, color, sibling, up) => identity,
    }
}

theorem erase_spine_focus_parent_consistent(spine: EraseSpine, tree: RbTree, anchor: struct rb_node*) {
    requires rb_parent_consistent(plug(erase_context(spine), tree), anchor) == 1;
    ensures rb_parent_consistent(tree, erase_spine_parent(spine, anchor)) == 1 by {
        induct(spine) as ih {
            EraseSpine::Top => {
                unfold(erase_spine_parent(EraseSpine::Top, anchor));
                have plug(erase_context(EraseSpine::Top), tree) == tree by {
                    unfold(erase_context(EraseSpine::Top)); unfold(plug(Context::Top, tree)); normalize();
                }
                rewrite(tree == plug(erase_context(EraseSpine::Top), tree)); assumption();
            },
            EraseSpine::Left(identity, parent, color, sibling, up) => {
                have erase_context(EraseSpine::Left(identity, parent, color, sibling, up)) == Context::Left(identity, parent, color, sibling, erase_context(up)) by {
                    unfold(erase_context(EraseSpine::Left(identity, parent, color, sibling, up))); normalize();
                }
                have rb_parent_consistent(plug(Context::Left(identity, parent, color, sibling, erase_context(up)), tree), anchor) == 1 by {
                    rewrite(Context::Left(identity, parent, color, sibling, erase_context(up)) == erase_context(EraseSpine::Left(identity, parent, color, sibling, up))); assumption();
                }
                apply(plug_parent_consistent_ctx(Context::Left(identity, parent, color, sibling, erase_context(up)), tree, anchor));
                apply(ctx_consistent_left_focus(identity, parent, color, sibling, erase_context(up), tree, anchor));
                unfold(erase_spine_parent(EraseSpine::Left(identity, parent, color, sibling, up), anchor)); assumption();
            },
        }
    }
}

# The path with its innermost left link exposed for the C successor splice.

function erase_minimum_identity(minimum: RbMinimum) -> struct rb_node* {
    match minimum {
        RbMinimum::Absent => 0,
        RbMinimum::Found(identity, color, child) => identity,
    }
}

function erase_minimum_child(minimum: RbMinimum) -> RbTree {
    match minimum {
        RbMinimum::Absent => RbTree::Empty,
        RbMinimum::Found(identity, color, child) => child,
    }
}

function erase_minimum_color(minimum: RbMinimum) -> Color {
    match minimum {
        RbMinimum::Absent => Color::Black,
        RbMinimum::Found(identity, color, child) => color,
    }
}

theorem erase_spine_min_parent(spine: EraseSpine, tree: RbTree) {
    requires tree != RbTree::Empty;
    ensures rb_min_parent(plug(erase_context(spine), tree)) == rb_min_parent(tree) by {
        induct(spine) as ih {
            EraseSpine::Top => {
                unfold(erase_context(EraseSpine::Top));
                unfold(plug(Context::Top, tree)); normalize();
            }
            EraseSpine::Left(identity, parent, color, sibling, up) => {
                have RbTree::Node(identity, parent, color, tree, sibling) != RbTree::Empty by { normalize(); }
                apply(ih(up, RbTree::Node(identity, parent, color, tree, sibling)));
                apply(rb_min_parent_nonempty_left(identity, parent, color, tree, sibling));
                unfold(erase_context(EraseSpine::Left(identity, parent, color, sibling, up)));
                unfold(plug(Context::Left(identity, parent, color, sibling, erase_context(up)), tree));
                rewrite(rb_min_parent(plug(erase_context(up), RbTree::Node(identity, parent, color, tree, sibling)))
                    == rb_min_parent(RbTree::Node(identity, parent, color, tree, sibling)));
                assumption();
            }
        }
    }
}

theorem erase_spine_min_context(spine: EraseSpine, tree: RbTree, outer: Context) {
    requires tree != RbTree::Empty;
    ensures rb_min_context(plug(erase_context(spine), tree), outer)
        == rb_min_context(tree, ctx_concat(erase_context(spine), outer)) by {
        induct(spine) as ih {
            EraseSpine::Top => {
                unfold(erase_context(EraseSpine::Top));
                unfold(plug(Context::Top, tree));
                unfold(ctx_concat(Context::Top, outer)); normalize();
            }
            EraseSpine::Left(identity, parent, color, sibling, up) => {
                have RbTree::Node(identity, parent, color, tree, sibling) != RbTree::Empty by { normalize(); }
                apply(ih(up, RbTree::Node(identity, parent, color, tree, sibling), outer));
                apply(rb_min_context_nonempty_left(identity, parent, color, tree, sibling,
                    ctx_concat(erase_context(up), outer)));
                unfold(erase_context(EraseSpine::Left(identity, parent, color, sibling, up)));
                unfold(plug(Context::Left(identity, parent, color, sibling, erase_context(up)), tree));
                unfold(ctx_concat(Context::Left(identity, parent, color, sibling, erase_context(up)), outer));
                rewrite(rb_min_context(plug(erase_context(up), RbTree::Node(identity, parent, color, tree, sibling)), outer)
                    == rb_min_context(RbTree::Node(identity, parent, color, tree, sibling), ctx_concat(erase_context(up), outer)));
                assumption();
            }
        }
    }
}

function erase_spine_links(spine: EraseSpine, anchor: struct rb_node*) -> int32
    decreases spine
{
    match spine {
        EraseSpine::Top => 1,
        EraseSpine::Left(identity, parent, color, sibling, up) =>
            if parent == erase_spine_parent(up, anchor) { erase_spine_links(up, anchor) } else { 0 },
    }
}

theorem erase_spine_links_from_tree(spine: EraseSpine, tree: RbTree, anchor: struct rb_node*) {
    requires rb_parent_consistent(plug(erase_context(spine), tree), anchor) == 1;
    ensures erase_spine_links(spine, anchor) == 1 by {
        induct(spine) as ih {
            EraseSpine::Top => { unfold(erase_spine_links(EraseSpine::Top, anchor)); normalize(); }
            EraseSpine::Left(identity, parent, color, sibling, up) => {
                have plug(erase_context(EraseSpine::Left(identity, parent, color, sibling, up)), tree)
                    == plug(erase_context(up), RbTree::Node(identity, parent, color, tree, sibling)) by {
                    unfold(erase_context(EraseSpine::Left(identity, parent, color, sibling, up)));
                    unfold(plug(Context::Left(identity, parent, color, sibling, erase_context(up)), tree)); normalize();
                }
                have rb_parent_consistent(plug(erase_context(up), RbTree::Node(identity, parent, color, tree, sibling)), anchor) == 1 by {
                    rewrite(plug(erase_context(up), RbTree::Node(identity, parent, color, tree, sibling))
                        == plug(erase_context(EraseSpine::Left(identity, parent, color, sibling, up)), tree)); assumption();
                }
                apply(ih(up, RbTree::Node(identity, parent, color, tree, sibling), anchor));
                apply(erase_spine_focus_parent_consistent(up, RbTree::Node(identity, parent, color, tree, sibling), anchor));
                apply(erase_parent_consistent_parent_is(RbTree::Node(identity, parent, color, tree, sibling), erase_spine_parent(up, anchor)));
                apply(rb_parent_is_node_parent(identity, parent, color, tree, sibling, erase_spine_parent(up, anchor)));
                unfold(erase_spine_links(EraseSpine::Left(identity, parent, color, sibling, up), anchor));
                rewrite(parent == erase_spine_parent(up, anchor));
                rewrite(erase_spine_links(up, anchor) == 1); normalize();
            }
        }
    }
}

theorem erase_spine_context_parent(spine: EraseSpine, anchor: struct rb_node*, parent: struct rb_node*,
        color: Color, sibling: RbTree, above: Context) {
    ensures ctx_node_is(ctx_concat(erase_context(spine), Context::Left(anchor, parent, color, sibling, above)),
        erase_spine_parent(spine, anchor)) == 1 by {
        induct(spine) as ih {
            EraseSpine::Top => {
                unfold(erase_context(EraseSpine::Top));
                unfold(erase_spine_parent(EraseSpine::Top, anchor));
                unfold(ctx_concat(Context::Top, Context::Left(anchor, parent, color, sibling, above)));
                unfold(ctx_node_is(Context::Left(anchor, parent, color, sibling, above), anchor)); normalize();
            }
            EraseSpine::Left(id, gp, c, s, up) => {
                unfold(erase_context(EraseSpine::Left(id, gp, c, s, up)));
                unfold(erase_spine_parent(EraseSpine::Left(id, gp, c, s, up), anchor));
                unfold(ctx_concat(Context::Left(id, gp, c, s, erase_context(up)), Context::Left(anchor, parent, color, sibling, above)));
                unfold(ctx_node_is(Context::Left(id, gp, c, s,
                    ctx_concat(erase_context(up), Context::Left(anchor, parent, color, sibling, above))), id)); normalize();
            }
        }
    }
    ensures ctx_concat(erase_context(spine), Context::Left(anchor, parent, color, sibling, above))
        == ctx_reroot(ctx_concat(erase_context(spine), Context::Left(anchor, parent, color, sibling, above)),
            erase_spine_parent(spine, anchor)) by {
        induct(spine) as ih {
            EraseSpine::Top => {
                unfold(erase_context(EraseSpine::Top));
                unfold(erase_spine_parent(EraseSpine::Top, anchor));
                unfold(ctx_concat(Context::Top, Context::Left(anchor, parent, color, sibling, above)));
                unfold(ctx_reroot(Context::Left(anchor, parent, color, sibling, above), anchor)); normalize();
            }
            EraseSpine::Left(id, gp, c, s, up) => {
                unfold(erase_context(EraseSpine::Left(id, gp, c, s, up)));
                unfold(erase_spine_parent(EraseSpine::Left(id, gp, c, s, up), anchor));
                unfold(ctx_concat(Context::Left(id, gp, c, s, erase_context(up)), Context::Left(anchor, parent, color, sibling, above)));
                unfold(ctx_reroot(Context::Left(id, gp, c, s,
                    ctx_concat(erase_context(up), Context::Left(anchor, parent, color, sibling, above))), id)); normalize();
            }
        }
    }
}

spec enum EraseAnchorFrame {
    At(struct rb_node*, Color, RbTree, Context),
}

function erase_anchor_context(anchor: struct rb_node*, frame: EraseAnchorFrame) -> Context {
    match frame {
        EraseAnchorFrame::At(parent, color, sibling, above) => Context::Left(anchor, parent, color, sibling, above),
    }
}
