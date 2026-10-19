arithmetic "integer";

// Remaining insertion flips, with an arbitrary owned black-parent boundary.
verifying "rb_insert_augmented.c";
verifying "rbtree_size_compute.c";
verifying "rbtree_size_copy.c";
import "rbtree_size_context_resources.click";
import "rbtree_size_recolor.click";

spec enum SizedFlipChain {
    Root,
    Stop(SizedContext),
    LL(struct rb_node*, struct rb_node*, int32, int32, SizedTree, SizedTree, SizedFlipChain),
    LR(struct rb_node*, struct rb_node*, int32, int32, SizedTree, SizedTree, SizedFlipChain),
    RL(struct rb_node*, struct rb_node*, int32, int32, SizedTree, SizedTree, SizedFlipChain),
    RR(struct rb_node*, struct rb_node*, int32, int32, SizedTree, SizedTree, SizedFlipChain),
}

function sized_flip_parent(chain: SizedFlipChain) -> struct rb_node* {
    match chain {
        SizedFlipChain::Root => 0,
        SizedFlipChain::Stop(ctx) => sized_context_parent(ctx, 0),
        SizedFlipChain::LL(p, g, pv, gv, other, uncle, up) => p,
        SizedFlipChain::LR(p, g, pv, gv, other, uncle, up) => p,
        SizedFlipChain::RL(p, g, pv, gv, other, uncle, up) => p,
        SizedFlipChain::RR(p, g, pv, gv, other, uncle, up) => p,
    }
}

function sized_flip_context(chain: SizedFlipChain) -> SizedContext
    decreases chain
{
    match chain {
        SizedFlipChain::Root => SizedContext::Top,
        SizedFlipChain::Stop(ctx) => ctx,
        SizedFlipChain::LL(p, g, pv, gv, other, uncle, up) => SizedContext::Left(p, g, Color::Red, pv, other, SizedContext::Left(g, sized_flip_parent(up), Color::Black, gv, uncle, sized_flip_context(up))),
        SizedFlipChain::LR(p, g, pv, gv, other, uncle, up) => SizedContext::Right(p, g, Color::Red, pv, other, SizedContext::Left(g, sized_flip_parent(up), Color::Black, gv, uncle, sized_flip_context(up))),
        SizedFlipChain::RL(p, g, pv, gv, other, uncle, up) => SizedContext::Left(p, g, Color::Red, pv, other, SizedContext::Right(g, sized_flip_parent(up), Color::Black, gv, uncle, sized_flip_context(up))),
        SizedFlipChain::RR(p, g, pv, gv, other, uncle, up) => SizedContext::Right(p, g, Color::Red, pv, other, SizedContext::Right(g, sized_flip_parent(up), Color::Black, gv, uncle, sized_flip_context(up))),
    }
}

function sized_flip_depth(chain: SizedFlipChain) -> Integer
    decreases chain
{
    match chain {
        SizedFlipChain::Root => 0,
        SizedFlipChain::Stop(ctx) => 0,
        SizedFlipChain::LL(p, g, pv, gv, other, uncle, up) => sized_flip_depth(up) + 1,
        SizedFlipChain::LR(p, g, pv, gv, other, uncle, up) => sized_flip_depth(up) + 1,
        SizedFlipChain::RL(p, g, pv, gv, other, uncle, up) => sized_flip_depth(up) + 1,
        SizedFlipChain::RR(p, g, pv, gv, other, uncle, up) => sized_flip_depth(up) + 1,
    }
}

function sized_flip_uncle_red(uncle: SizedTree) -> int32 {
    match uncle {
        SizedTree::Empty => 0,
        SizedTree::Node(node, parent, color, value, left, right) =>
            if color == Color::Red { 1 } else { 0 },
    }
}
function sized_flip_black_boundary(ctx: SizedContext) -> int32 {
    match ctx {
        SizedContext::Top => 0,
        SizedContext::Left(node, parent, color, value, sibling, up) => color_bit(color),
        SizedContext::Right(node, parent, color, value, sibling, up) => color_bit(color),
    }
}
function sized_flip_allowed(chain: SizedFlipChain) -> int32
    decreases chain
{
    match chain {
        SizedFlipChain::Root => 1,
        SizedFlipChain::Stop(ctx) => sized_flip_black_boundary(ctx),
        SizedFlipChain::LL(p, g, pv, gv, other, uncle, up) => if sized_flip_uncle_red(uncle) == 1 { sized_flip_allowed(up) } else { 0 },
        SizedFlipChain::LR(p, g, pv, gv, other, uncle, up) => if sized_flip_uncle_red(uncle) == 1 { sized_flip_allowed(up) } else { 0 },
        SizedFlipChain::RL(p, g, pv, gv, other, uncle, up) => if sized_flip_uncle_red(uncle) == 1 { sized_flip_allowed(up) } else { 0 },
        SizedFlipChain::RR(p, g, pv, gv, other, uncle, up) => if sized_flip_uncle_red(uncle) == 1 { sized_flip_allowed(up) } else { 0 },
    }
}

function sized_flip_result(chain: SizedFlipChain, sub: SizedTree) -> SizedTree
    decreases chain
{
    match chain {
        SizedFlipChain::Root => sized_recolor(sub, Color::Black),
        SizedFlipChain::Stop(ctx) => sized_plug(ctx, sub),
        SizedFlipChain::LL(p, g, pv, gv, other, uncle, up) => sized_flip_result(up, SizedTree::Node(g, sized_flip_parent(up), Color::Red, gv, SizedTree::Node(p, g, Color::Black, pv, sub, other), sized_recolor(uncle, Color::Black))),
        SizedFlipChain::LR(p, g, pv, gv, other, uncle, up) => sized_flip_result(up, SizedTree::Node(g, sized_flip_parent(up), Color::Red, gv, SizedTree::Node(p, g, Color::Black, pv, other, sub), sized_recolor(uncle, Color::Black))),
        SizedFlipChain::RL(p, g, pv, gv, other, uncle, up) => sized_flip_result(up, SizedTree::Node(g, sized_flip_parent(up), Color::Red, gv, sized_recolor(uncle, Color::Black), SizedTree::Node(p, g, Color::Black, pv, sub, other))),
        SizedFlipChain::RR(p, g, pv, gv, other, uncle, up) => sized_flip_result(up, SizedTree::Node(g, sized_flip_parent(up), Color::Red, gv, sized_recolor(uncle, Color::Black), SizedTree::Node(p, g, Color::Black, pv, other, sub))),
    }
}

theorem sized_flip_depth_nonnegative(chain: SizedFlipChain) {
    ensures 0 <= sized_flip_depth(chain) by {
        induct(chain) as ih {
            SizedFlipChain::Root => { unfold(sized_flip_depth(SizedFlipChain::Root)); normalize(); },
            SizedFlipChain::Stop(ctx) => { unfold(sized_flip_depth(SizedFlipChain::Stop(ctx))); normalize(); },
            SizedFlipChain::LL(p, g, pv, gv, other, uncle, up) => { apply(ih(up)); unfold(sized_flip_depth(SizedFlipChain::LL(p, g, pv, gv, other, uncle, up))); arithmetic() using { 0 <= sized_flip_depth(up); }; },
            SizedFlipChain::LR(p, g, pv, gv, other, uncle, up) => { apply(ih(up)); unfold(sized_flip_depth(SizedFlipChain::LR(p, g, pv, gv, other, uncle, up))); arithmetic() using { 0 <= sized_flip_depth(up); }; },
            SizedFlipChain::RL(p, g, pv, gv, other, uncle, up) => { apply(ih(up)); unfold(sized_flip_depth(SizedFlipChain::RL(p, g, pv, gv, other, uncle, up))); arithmetic() using { 0 <= sized_flip_depth(up); }; },
            SizedFlipChain::RR(p, g, pv, gv, other, uncle, up) => { apply(ih(up)); unfold(sized_flip_depth(SizedFlipChain::RR(p, g, pv, gv, other, uncle, up))); arithmetic() using { 0 <= sized_flip_depth(up); }; },
    }
    }
}

theorem sized_flip_context_parent(chain: SizedFlipChain) {
    ensures sized_context_parent(sized_flip_context(chain), 0) == sized_flip_parent(chain) by {
        match chain {
            SizedFlipChain::Root => {
                rewrite(chain == SizedFlipChain::Root);
                unfold(sized_flip_context(SizedFlipChain::Root));
                unfold(sized_context_parent(SizedContext::Top, 0));
                unfold(sized_flip_parent(SizedFlipChain::Root)); normalize();
            },
            SizedFlipChain::Stop(ctx) => {
                rewrite(chain == SizedFlipChain::Stop(ctx));
                unfold(sized_flip_context(SizedFlipChain::Stop(ctx)));
                unfold(sized_flip_parent(SizedFlipChain::Stop(ctx))); normalize();
            },
            SizedFlipChain::LL(p, g, pv, gv, other, uncle, up) => {
                rewrite(chain == SizedFlipChain::LL(p, g, pv, gv, other, uncle, up));
                unfold(sized_flip_context(SizedFlipChain::LL(p, g, pv, gv, other, uncle, up)));
                unfold(sized_context_parent(SizedContext::Left(p, g, Color::Red, pv, other, SizedContext::Left(g, sized_flip_parent(up), Color::Black, gv, uncle, sized_flip_context(up))), 0));
                unfold(sized_flip_parent(SizedFlipChain::LL(p, g, pv, gv, other, uncle, up))); normalize();
            },
            SizedFlipChain::LR(p, g, pv, gv, other, uncle, up) => {
                rewrite(chain == SizedFlipChain::LR(p, g, pv, gv, other, uncle, up));
                unfold(sized_flip_context(SizedFlipChain::LR(p, g, pv, gv, other, uncle, up)));
                unfold(sized_context_parent(SizedContext::Right(p, g, Color::Red, pv, other, SizedContext::Left(g, sized_flip_parent(up), Color::Black, gv, uncle, sized_flip_context(up))), 0));
                unfold(sized_flip_parent(SizedFlipChain::LR(p, g, pv, gv, other, uncle, up))); normalize();
            },
            SizedFlipChain::RL(p, g, pv, gv, other, uncle, up) => {
                rewrite(chain == SizedFlipChain::RL(p, g, pv, gv, other, uncle, up));
                unfold(sized_flip_context(SizedFlipChain::RL(p, g, pv, gv, other, uncle, up)));
                unfold(sized_context_parent(SizedContext::Left(p, g, Color::Red, pv, other, SizedContext::Right(g, sized_flip_parent(up), Color::Black, gv, uncle, sized_flip_context(up))), 0));
                unfold(sized_flip_parent(SizedFlipChain::RL(p, g, pv, gv, other, uncle, up))); normalize();
            },
            SizedFlipChain::RR(p, g, pv, gv, other, uncle, up) => {
                rewrite(chain == SizedFlipChain::RR(p, g, pv, gv, other, uncle, up));
                unfold(sized_flip_context(SizedFlipChain::RR(p, g, pv, gv, other, uncle, up)));
                unfold(sized_context_parent(SizedContext::Right(p, g, Color::Red, pv, other, SizedContext::Right(g, sized_flip_parent(up), Color::Black, gv, uncle, sized_flip_context(up))), 0));
                unfold(sized_flip_parent(SizedFlipChain::RR(p, g, pv, gv, other, uncle, up))); normalize();
            },
    }
    }
}

function sized_flip_node(tree: SizedTree) -> struct rb_node* {
    match tree {
        SizedTree::Empty => 0,
        SizedTree::Node(node, parent, color, value, left, right) => node,
    }
}

function sized_flip_stopped(chain: SizedFlipChain) -> int32 {
    match chain {
        SizedFlipChain::Root => 1,
        SizedFlipChain::Stop(ctx) => 1,
        SizedFlipChain::LL(p, g, pv, gv, other, uncle, up) => 0,
        SizedFlipChain::LR(p, g, pv, gv, other, uncle, up) => 0,
        SizedFlipChain::RL(p, g, pv, gv, other, uncle, up) => 0,
        SizedFlipChain::RR(p, g, pv, gv, other, uncle, up) => 0,
    }
}

function sized_flip_color(tree: SizedTree) -> int32 {
    match tree {
        SizedTree::Empty => 1,
        SizedTree::Node(node, parent, color, value, left, right) => color_bit(color),
    }
}
