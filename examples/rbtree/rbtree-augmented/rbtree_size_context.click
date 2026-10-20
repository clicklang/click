arithmetic "integer";

// Ancestor frames retain cached sizes and untouched sibling subtrees.
verifying "rbtree_size_compute.c";
verifying "rbtree_size_copy.c";
import "rbtree_size_model.click";

spec enum SizedContext {
    Top,
    Left(struct rb_node*, struct rb_node*, Color, int32, SizedTree, SizedContext),
    Right(struct rb_node*, struct rb_node*, Color, int32, SizedTree, SizedContext),
}

function sized_context_shape(ctx: SizedContext) -> Context
    decreases ctx
{
    match ctx {
        SizedContext::Top => Context::Top,
        SizedContext::Left(node, parent, color, value, sibling, up) =>
            Context::Left(node, parent, color, sized_shape(sibling), sized_context_shape(up)),
        SizedContext::Right(node, parent, color, value, sibling, up) =>
            Context::Right(node, parent, color, sized_shape(sibling), sized_context_shape(up)),
    }
}

function sized_plug(ctx: SizedContext, sub: SizedTree) -> SizedTree
    decreases ctx
{
    match ctx {
        SizedContext::Top => sub,
        SizedContext::Left(node, parent, color, value, sibling, up) =>
            sized_plug(up, SizedTree::Node(node, parent, color, value, sub, sibling)),
        SizedContext::Right(node, parent, color, value, sibling, up) =>
            sized_plug(up, SizedTree::Node(node, parent, color, value, sibling, sub)),
    }
}

function sized_context_depth(ctx: SizedContext) -> Integer
    decreases ctx
{
    match ctx {
        SizedContext::Top => 0,
        SizedContext::Left(node, parent, color, value, sibling, up) => sized_context_depth(up) + 1,
        SizedContext::Right(node, parent, color, value, sibling, up) => sized_context_depth(up) + 1,
    }
}

// Remaining ancestors are coherent with the previously cached hole size.
function sized_context_valid(ctx: SizedContext, hole: Integer) -> int32
    decreases ctx
{
    match ctx {
        SizedContext::Top => 1,
        SizedContext::Left(node, parent, color, value, sibling, up) =>
            if to_integer(value) == 1 + hole + to_integer(sized_value(sibling))
            {
                if sized_counts_valid(sibling) == 1 {
                    if sized_context_valid(up, to_integer(value)) == 1 { 1 } else { 0 }
                } else { 0 }
            } else { 0 },
        SizedContext::Right(node, parent, color, value, sibling, up) =>
            if to_integer(value) == 1 + to_integer(sized_value(sibling)) + hole
            {
                if sized_counts_valid(sibling) == 1 {
                    if sized_context_valid(up, to_integer(value)) == 1 { 1 } else { 0 }
                } else { 0 }
            } else { 0 },
    }
}

theorem sized_plug_preserves_shape(ctx: SizedContext, sub: SizedTree) {
    ensures sized_shape(sized_plug(ctx, sub)) == plug(sized_context_shape(ctx), sized_shape(sub)) by {
        induct(ctx) as ih {
            SizedContext::Top => {
                unfold(sized_plug(SizedContext::Top, sub));
                unfold(sized_context_shape(SizedContext::Top));
                unfold(plug(Context::Top, sized_shape(sub)));
                normalize();
            },
            SizedContext::Left(node, parent, color, value, sibling, up) => {
                apply(ih(up, SizedTree::Node(node, parent, color, value, sub, sibling)));
                unfold(sized_plug(SizedContext::Left(node, parent, color, value, sibling, up), sub));
                unfold(sized_context_shape(SizedContext::Left(node, parent, color, value, sibling, up)));
                unfold(plug(Context::Left(node, parent, color, sized_shape(sibling), sized_context_shape(up)), sized_shape(sub)));
                unfold(sized_shape(SizedTree::Node(node, parent, color, value, sub, sibling)));
                assumption();
            },
            SizedContext::Right(node, parent, color, value, sibling, up) => {
                apply(ih(up, SizedTree::Node(node, parent, color, value, sibling, sub)));
                unfold(sized_plug(SizedContext::Right(node, parent, color, value, sibling, up), sub));
                unfold(sized_context_shape(SizedContext::Right(node, parent, color, value, sibling, up)));
                unfold(plug(Context::Right(node, parent, color, sized_shape(sibling), sized_context_shape(up)), sized_shape(sub)));
                unfold(sized_shape(SizedTree::Node(node, parent, color, value, sibling, sub)));
                assumption();
            },
        }
    }
}

theorem sized_context_depth_nonnegative(ctx: SizedContext) {
    ensures 0 <= sized_context_depth(ctx) by {
        induct(ctx) as ih {
            SizedContext::Top => { unfold(sized_context_depth(SizedContext::Top)); normalize(); },
            SizedContext::Left(node, parent, color, value, sibling, up) => {
                apply(ih(up));
                unfold(sized_context_depth(SizedContext::Left(node, parent, color, value, sibling, up)));
                arithmetic() using { 0 <= sized_context_depth(up); };
            },
            SizedContext::Right(node, parent, color, value, sibling, up) => {
                apply(ih(up));
                unfold(sized_context_depth(SizedContext::Right(node, parent, color, value, sibling, up)));
                arithmetic() using { 0 <= sized_context_depth(up); };
            },
        }
    }
}

// If recomputation leaves the hole's cached size unchanged, no ancestor write
// is needed: every remaining cached count is still correct.
theorem sized_context_early_stop(ctx: SizedContext, sub: SizedTree, previous: int32) {
    requires sized_counts_valid(sub) == 1;
    requires sized_value(sub) == previous;
    requires sized_context_valid(ctx, to_integer(previous)) == 1;
    ensures sized_counts_valid(sized_plug(ctx, sub)) == 1 by {
        induct(ctx) as ih {
            SizedContext::Top => {
                unfold(sized_plug(SizedContext::Top, sub));
                assumption();
            },
            SizedContext::Left(node, parent, color, value, sibling, up) => {
                unfold(sized_context_valid(SizedContext::Left(node, parent, color, value, sibling, up), to_integer(previous)));
                have to_integer(value) == 1 + to_integer(previous) + to_integer(sized_value(sibling)) by auto();
                have sized_counts_valid(sibling) == 1 by auto();
                have sized_context_valid(up, to_integer(value)) == 1 by auto();
                have sized_counts_valid(SizedTree::Node(node, parent, color, value, sub, sibling)) == 1 by {
                    unfold(sized_counts_valid(SizedTree::Node(node, parent, color, value, sub, sibling)));
                    rewrite(sized_value(sub) == previous);
                    normalize() using { to_integer(value) == 1 + to_integer(previous) + to_integer(sized_value(sibling)); sized_counts_valid(sub) == 1; sized_counts_valid(sibling) == 1; };
                }
                have sized_value(SizedTree::Node(node, parent, color, value, sub, sibling)) == value by {
                    unfold(sized_value(SizedTree::Node(node, parent, color, value, sub, sibling))); normalize();
                }
                apply(ih(up, SizedTree::Node(node, parent, color, value, sub, sibling), value));
                unfold(sized_plug(SizedContext::Left(node, parent, color, value, sibling, up), sub));
                assumption();
            },
            SizedContext::Right(node, parent, color, value, sibling, up) => {
                unfold(sized_context_valid(SizedContext::Right(node, parent, color, value, sibling, up), to_integer(previous)));
                have to_integer(value) == 1 + to_integer(sized_value(sibling)) + to_integer(previous) by auto();
                have sized_counts_valid(sibling) == 1 by auto();
                have sized_context_valid(up, to_integer(value)) == 1 by auto();
                have sized_counts_valid(SizedTree::Node(node, parent, color, value, sibling, sub)) == 1 by {
                    unfold(sized_counts_valid(SizedTree::Node(node, parent, color, value, sibling, sub)));
                    rewrite(sized_value(sub) == previous);
                    normalize() using { to_integer(value) == 1 + to_integer(sized_value(sibling)) + to_integer(previous); sized_counts_valid(sub) == 1; sized_counts_valid(sibling) == 1; };
                }
                have sized_value(SizedTree::Node(node, parent, color, value, sibling, sub)) == value by {
                    unfold(sized_value(SizedTree::Node(node, parent, color, value, sibling, sub))); normalize();
                }
                apply(ih(up, SizedTree::Node(node, parent, color, value, sibling, sub), value));
                unfold(sized_plug(SizedContext::Right(node, parent, color, value, sibling, up), sub));
                assumption();
            },
        }
    }
}

// A bound on the reconstructed tree also bounds every visited subtree. This
// lets propagation reuse the original whole-tree bound for checked size sums.
theorem sized_plug_contains_focus(ctx: SizedContext, sub: SizedTree) {
    ensures rb_subtree_size(sized_shape(sub)) <= rb_subtree_size(sized_shape(sized_plug(ctx, sub))) by {
        induct(ctx) as ih {
            SizedContext::Top => {
                unfold(sized_plug(SizedContext::Top, sub));
                normalize();
            },
            SizedContext::Left(node, parent, color, value, sibling, up) => {
                apply(rb_subtree_size_nonnegative(sized_shape(sibling)));
                have rb_subtree_size(sized_shape(sub)) <= rb_subtree_size(sized_shape(SizedTree::Node(node, parent, color, value, sub, sibling))) by {
                    unfold(sized_shape(SizedTree::Node(node, parent, color, value, sub, sibling)));
                    unfold(rb_subtree_size(RbTree::Node(node, parent, color, sized_shape(sub), sized_shape(sibling))));
                    arithmetic() using { rb_subtree_size(sized_shape(sibling)) >= 0; };
                }
                apply(ih(up, SizedTree::Node(node, parent, color, value, sub, sibling)));
                have rb_subtree_size(sized_shape(sub)) <= rb_subtree_size(sized_shape(sized_plug(up, SizedTree::Node(node, parent, color, value, sub, sibling)))) by {
                    arithmetic() using {
                        rb_subtree_size(sized_shape(sub)) <= rb_subtree_size(sized_shape(SizedTree::Node(node, parent, color, value, sub, sibling)));
                        rb_subtree_size(sized_shape(SizedTree::Node(node, parent, color, value, sub, sibling))) <= rb_subtree_size(sized_shape(sized_plug(up, SizedTree::Node(node, parent, color, value, sub, sibling))));
                    };
                }
                unfold(sized_plug(SizedContext::Left(node, parent, color, value, sibling, up), sub));
                assumption();
            },
            SizedContext::Right(node, parent, color, value, sibling, up) => {
                apply(rb_subtree_size_nonnegative(sized_shape(sibling)));
                have rb_subtree_size(sized_shape(sub)) <= rb_subtree_size(sized_shape(SizedTree::Node(node, parent, color, value, sibling, sub))) by {
                    unfold(sized_shape(SizedTree::Node(node, parent, color, value, sibling, sub)));
                    unfold(rb_subtree_size(RbTree::Node(node, parent, color, sized_shape(sibling), sized_shape(sub))));
                    arithmetic() using { rb_subtree_size(sized_shape(sibling)) >= 0; };
                }
                apply(ih(up, SizedTree::Node(node, parent, color, value, sibling, sub)));
                have rb_subtree_size(sized_shape(sub)) <= rb_subtree_size(sized_shape(sized_plug(up, SizedTree::Node(node, parent, color, value, sibling, sub)))) by {
                    arithmetic() using {
                        rb_subtree_size(sized_shape(sub)) <= rb_subtree_size(sized_shape(SizedTree::Node(node, parent, color, value, sibling, sub)));
                        rb_subtree_size(sized_shape(SizedTree::Node(node, parent, color, value, sibling, sub))) <= rb_subtree_size(sized_shape(sized_plug(up, SizedTree::Node(node, parent, color, value, sibling, sub))));
                    };
                }
                unfold(sized_plug(SizedContext::Right(node, parent, color, value, sibling, up), sub));
                assumption();
            },
        }
    }
}

// Recomputing metadata leaves the surrounding tree shape unchanged.
theorem sized_plug_same_shape(ctx: SizedContext, before: SizedTree, after: SizedTree) {
    requires sized_shape(before) == sized_shape(after);
    ensures sized_shape(sized_plug(ctx, before)) == sized_shape(sized_plug(ctx, after)) by {
        apply(sized_plug_preserves_shape(ctx, before));
        apply(sized_plug_preserves_shape(ctx, after));
        rewrite(sized_shape(sized_plug(ctx, before)) == plug(sized_context_shape(ctx), sized_shape(before)));
        rewrite(sized_shape(sized_plug(ctx, after)) == plug(sized_context_shape(ctx), sized_shape(after)));
        rewrite(sized_shape(before) == sized_shape(after)); assumption();
    }
}
