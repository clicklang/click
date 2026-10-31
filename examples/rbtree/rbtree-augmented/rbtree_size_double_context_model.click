// Lift double-rotation model preservation through an arbitrary ancestor path.
verifying "rbtree_size_compute.c";
verifying "rbtree_size_copy.c";
import "rbtree_size_double_preserves_counts.click";
import "rbtree_size_context.click";

theorem sized_double_context_counts(ctx: SizedContext, g: struct rb_node*, p: struct rb_node*, node: struct rb_node*, above: struct rb_node*,
    nv: int32, pv: int32, gv: int32, pc: int32, gc: int32,
    far: SizedTree, ml: SizedTree, mr: SizedTree, uncle: SizedTree) {
    requires sized_counts_valid(sized_context_double_subtree_before(g, p, node, above, nv, pv, gv, far, ml, mr, uncle)) == 1;
    requires sized_context_valid(ctx, to_integer(gv)) == 1;
    requires to_integer(pc) == 1 + to_integer(sized_value(far)) + to_integer(sized_value(ml));
    requires to_integer(gc) == 1 + to_integer(sized_value(mr)) + to_integer(sized_value(uncle));
    ensures sized_counts_valid(sized_plug(ctx, sized_double_cached_after(g, p, node, above, gv, pc, gc, far, ml, mr, uncle))) == 1 by {
        apply(sized_double_preserves_counts(g, p, node, above, nv, pv, gv, pc, gc, far, ml, mr, uncle));
        have sized_value(sized_double_cached_after(g, p, node, above, gv, pc, gc, far, ml, mr, uncle)) == gv by {
            unfold(sized_double_cached_after(g, p, node, above, gv, pc, gc, far, ml, mr, uncle));
            unfold(sized_value(SizedTree::Node(node, above, Color::Black, gv, SizedTree::Node(p, node, Color::Red, pc, far, sized_reparent(ml, p)), SizedTree::Node(g, node, Color::Red, gc, sized_reparent(mr, g), uncle))));
            normalize();
        }
        apply(sized_context_early_stop(ctx, sized_double_cached_after(g, p, node, above, gv, pc, gc, far, ml, mr, uncle), gv));
        assumption();
    }
}

theorem sized_double_context_inorder(ctx: SizedContext, g: struct rb_node*, p: struct rb_node*, node: struct rb_node*, above: struct rb_node*,
    nv: int32, pv: int32, gv: int32, pc: int32, gc: int32,
    far: SizedTree, ml: SizedTree, mr: SizedTree, uncle: SizedTree) {
    ensures rb_inorder(sized_shape(sized_plug(ctx, sized_double_cached_after(g, p, node, above, gv, pc, gc, far, ml, mr, uncle))))
        == rb_inorder(sized_shape(sized_plug(ctx, sized_context_double_subtree_before(g, p, node, above, nv, pv, gv, far, ml, mr, uncle)))) by {
        apply(sized_double_cached_inorder(g, p, node, above, gv, pc, gc, far, ml, mr, uncle, nv, pv));
        apply(sized_plug_preserves_shape(ctx, sized_double_cached_after(g, p, node, above, gv, pc, gc, far, ml, mr, uncle)));
        apply(sized_plug_preserves_shape(ctx, sized_context_double_subtree_before(g, p, node, above, nv, pv, gv, far, ml, mr, uncle)));
        rewrite(sized_shape(sized_plug(ctx, sized_double_cached_after(g, p, node, above, gv, pc, gc, far, ml, mr, uncle))) == plug(sized_context_shape(ctx), sized_shape(sized_double_cached_after(g, p, node, above, gv, pc, gc, far, ml, mr, uncle))));
        rewrite(sized_shape(sized_plug(ctx, sized_context_double_subtree_before(g, p, node, above, nv, pv, gv, far, ml, mr, uncle))) == plug(sized_context_shape(ctx), sized_shape(sized_context_double_subtree_before(g, p, node, above, nv, pv, gv, far, ml, mr, uncle))));
        apply(plug_inorder_transport(sized_context_shape(ctx), sized_shape(sized_double_cached_after(g, p, node, above, gv, pc, gc, far, ml, mr, uncle)), sized_shape(sized_context_double_subtree_before(g, p, node, above, nv, pv, gv, far, ml, mr, uncle))));
        assumption();
    }
}

theorem sized_mirrored_double_context_counts(ctx: SizedContext, g: struct rb_node*, p: struct rb_node*, node: struct rb_node*, above: struct rb_node*,
    nv: int32, pv: int32, gv: int32, pc: int32, gc: int32,
    far: SizedTree, ml: SizedTree, mr: SizedTree, uncle: SizedTree) {
    requires sized_counts_valid(sized_mirrored_context_double_subtree_before(g, p, node, above, nv, pv, gv, far, ml, mr, uncle)) == 1;
    requires sized_context_valid(ctx, to_integer(gv)) == 1;
    requires to_integer(pc) == 1 + to_integer(sized_value(far)) + to_integer(sized_value(mr));
    requires to_integer(gc) == 1 + to_integer(sized_value(ml)) + to_integer(sized_value(uncle));
    ensures sized_counts_valid(sized_plug(ctx, sized_mirrored_double_cached_after(g, p, node, above, gv, pc, gc, far, ml, mr, uncle))) == 1 by {
        apply(sized_mirrored_double_preserves_counts(g, p, node, above, nv, pv, gv, pc, gc, far, ml, mr, uncle));
        have sized_value(sized_mirrored_double_cached_after(g, p, node, above, gv, pc, gc, far, ml, mr, uncle)) == gv by {
            unfold(sized_mirrored_double_cached_after(g, p, node, above, gv, pc, gc, far, ml, mr, uncle));
            unfold(sized_value(SizedTree::Node(node, above, Color::Black, gv, SizedTree::Node(g, node, Color::Red, gc, uncle, sized_reparent(ml, g)), SizedTree::Node(p, node, Color::Red, pc, sized_reparent(mr, p), far))));
            normalize();
        }
        apply(sized_context_early_stop(ctx, sized_mirrored_double_cached_after(g, p, node, above, gv, pc, gc, far, ml, mr, uncle), gv));
        assumption();
    }
}

theorem sized_mirrored_double_context_inorder(ctx: SizedContext, g: struct rb_node*, p: struct rb_node*, node: struct rb_node*, above: struct rb_node*,
    nv: int32, pv: int32, gv: int32, pc: int32, gc: int32,
    far: SizedTree, ml: SizedTree, mr: SizedTree, uncle: SizedTree) {
    ensures rb_inorder(sized_shape(sized_plug(ctx, sized_mirrored_double_cached_after(g, p, node, above, gv, pc, gc, far, ml, mr, uncle))))
        == rb_inorder(sized_shape(sized_plug(ctx, sized_mirrored_context_double_subtree_before(g, p, node, above, nv, pv, gv, far, ml, mr, uncle)))) by {
        apply(sized_mirrored_double_cached_inorder(g, p, node, above, gv, pc, gc, far, ml, mr, uncle, nv, pv));
        apply(sized_plug_preserves_shape(ctx, sized_mirrored_double_cached_after(g, p, node, above, gv, pc, gc, far, ml, mr, uncle)));
        apply(sized_plug_preserves_shape(ctx, sized_mirrored_context_double_subtree_before(g, p, node, above, nv, pv, gv, far, ml, mr, uncle)));
        rewrite(sized_shape(sized_plug(ctx, sized_mirrored_double_cached_after(g, p, node, above, gv, pc, gc, far, ml, mr, uncle))) == plug(sized_context_shape(ctx), sized_shape(sized_mirrored_double_cached_after(g, p, node, above, gv, pc, gc, far, ml, mr, uncle))));
        rewrite(sized_shape(sized_plug(ctx, sized_mirrored_context_double_subtree_before(g, p, node, above, nv, pv, gv, far, ml, mr, uncle))) == plug(sized_context_shape(ctx), sized_shape(sized_mirrored_context_double_subtree_before(g, p, node, above, nv, pv, gv, far, ml, mr, uncle))));
        apply(plug_inorder_transport(sized_context_shape(ctx), sized_shape(sized_mirrored_double_cached_after(g, p, node, above, gv, pc, gc, far, ml, mr, uncle)), sized_shape(sized_mirrored_context_double_subtree_before(g, p, node, above, nv, pv, gv, far, ml, mr, uncle))));
        assumption();
    }
}
