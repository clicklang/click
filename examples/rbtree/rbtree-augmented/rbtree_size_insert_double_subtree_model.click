// General inner insertion rotations retain arbitrary transferred subtrees.
verifying "rbtree_size_compute.c";
verifying "rbtree_size_copy.c";
import "rbtree_size_model.click";

function sized_context_double_subtree_before(g: struct rb_node*, p: struct rb_node*, node: struct rb_node*, above: struct rb_node*, nv: int32, pv: int32, gv: int32, far_left: SizedTree, middle_left: SizedTree, middle_right: SizedTree, uncle: SizedTree) -> SizedTree {
    SizedTree::Node(g, above, Color::Black, gv, SizedTree::Node(p, g, Color::Red, pv, far_left, SizedTree::Node(node, p, Color::Red, nv, middle_left, middle_right)), uncle)
}

function sized_context_double_subtree_after(g: struct rb_node*, p: struct rb_node*, node: struct rb_node*, above: struct rb_node*, far_left: SizedTree, middle_left: SizedTree, middle_right: SizedTree, uncle: SizedTree) -> RbTree {
    RbTree::Node(node, above, Color::Black, RbTree::Node(p, node, Color::Red, sized_shape(far_left), rb_reparent(sized_shape(middle_left), p)), RbTree::Node(g, node, Color::Red, rb_reparent(sized_shape(middle_right), g), sized_shape(uncle)))
}

theorem sized_context_double_subtree_matches_insert_fix(g: struct rb_node*, p: struct rb_node*, node: struct rb_node*, above: struct rb_node*, nv: int32, pv: int32, gv: int32, far_left: SizedTree, middle_left: SizedTree, middle_right: SizedTree, uncle: SizedTree) {
    ensures sized_context_double_subtree_after(g, p, node, above, far_left, middle_left, middle_right, uncle) == rb_insert_fix_outer_left(rb_insert_fix_inner_left(sized_shape(sized_context_double_subtree_before(g, p, node, above, nv, pv, gv, far_left, middle_left, middle_right, uncle)))) by {
        unfold(sized_context_double_subtree_before(g, p, node, above, nv, pv, gv, far_left, middle_left, middle_right, uncle));
        unfold(sized_shape(SizedTree::Node(g, above, Color::Black, gv, SizedTree::Node(p, g, Color::Red, pv, far_left, SizedTree::Node(node, p, Color::Red, nv, middle_left, middle_right)), uncle)));
        unfold(sized_shape(SizedTree::Node(p, g, Color::Red, pv, far_left, SizedTree::Node(node, p, Color::Red, nv, middle_left, middle_right))));
        unfold(sized_shape(SizedTree::Node(node, p, Color::Red, nv, middle_left, middle_right)));
        unfold(rb_insert_fix_inner_left(RbTree::Node(g, above, Color::Black, RbTree::Node(p, g, Color::Red, sized_shape(far_left), RbTree::Node(node, p, Color::Red, sized_shape(middle_left), sized_shape(middle_right))), sized_shape(uncle))));
        unfold(rb_rotate_left_at_left(RbTree::Node(g, above, Color::Black, RbTree::Node(p, g, Color::Red, sized_shape(far_left), RbTree::Node(node, p, Color::Red, sized_shape(middle_left), sized_shape(middle_right))), sized_shape(uncle))));
        unfold(rb_rotate_left(RbTree::Node(p, g, Color::Red, sized_shape(far_left), RbTree::Node(node, p, Color::Red, sized_shape(middle_left), sized_shape(middle_right)))));
        unfold(rb_insert_fix_outer_left(RbTree::Node(g, above, Color::Black, RbTree::Node(node, g, Color::Red, RbTree::Node(p, node, Color::Red, sized_shape(far_left), rb_reparent(sized_shape(middle_left), p)), sized_shape(middle_right)), sized_shape(uncle))));
        unfold(rb_rotate_right(RbTree::Node(g, above, Color::Black, RbTree::Node(node, g, Color::Red, RbTree::Node(p, node, Color::Red, sized_shape(far_left), rb_reparent(sized_shape(middle_left), p)), sized_shape(middle_right)), sized_shape(uncle))));
        unfold(rb_recolor_right(RbTree::Node(node, above, Color::Red, RbTree::Node(p, node, Color::Red, sized_shape(far_left), rb_reparent(sized_shape(middle_left), p)), RbTree::Node(g, node, Color::Black, rb_reparent(sized_shape(middle_right), g), sized_shape(uncle))), Color::Red));
        unfold(rb_recolor(RbTree::Node(g, node, Color::Black, rb_reparent(sized_shape(middle_right), g), sized_shape(uncle)), Color::Red));
        unfold(rb_recolor(RbTree::Node(node, above, Color::Red, RbTree::Node(p, node, Color::Red, sized_shape(far_left), rb_reparent(sized_shape(middle_left), p)), RbTree::Node(g, node, Color::Red, rb_reparent(sized_shape(middle_right), g), sized_shape(uncle))), Color::Black));
        unfold(sized_context_double_subtree_after(g, p, node, above, far_left, middle_left, middle_right, uncle));
        normalize();
    }
}

theorem sized_context_double_subtree_preserves_inorder(g: struct rb_node*, p: struct rb_node*, node: struct rb_node*, above: struct rb_node*, nv: int32, pv: int32, gv: int32, far_left: SizedTree, middle_left: SizedTree, middle_right: SizedTree, uncle: SizedTree) {
    ensures rb_inorder(sized_context_double_subtree_after(g, p, node, above, far_left, middle_left, middle_right, uncle)) == rb_inorder(sized_shape(sized_context_double_subtree_before(g, p, node, above, nv, pv, gv, far_left, middle_left, middle_right, uncle))) by {
        apply(sized_context_double_subtree_matches_insert_fix(g, p, node, above, nv, pv, gv, far_left, middle_left, middle_right, uncle));
        rewrite(sized_context_double_subtree_after(g, p, node, above, far_left, middle_left, middle_right, uncle) == rb_insert_fix_outer_left(rb_insert_fix_inner_left(sized_shape(sized_context_double_subtree_before(g, p, node, above, nv, pv, gv, far_left, middle_left, middle_right, uncle)))));
        apply(rb_insert_fix_outer_left_preserves_inorder(rb_insert_fix_inner_left(sized_shape(sized_context_double_subtree_before(g, p, node, above, nv, pv, gv, far_left, middle_left, middle_right, uncle)))));
        apply(rb_insert_fix_inner_left_preserves_inorder(sized_shape(sized_context_double_subtree_before(g, p, node, above, nv, pv, gv, far_left, middle_left, middle_right, uncle))));
        rewrite(rb_inorder(rb_insert_fix_outer_left(rb_insert_fix_inner_left(sized_shape(sized_context_double_subtree_before(g, p, node, above, nv, pv, gv, far_left, middle_left, middle_right, uncle))))) == rb_inorder(rb_insert_fix_inner_left(sized_shape(sized_context_double_subtree_before(g, p, node, above, nv, pv, gv, far_left, middle_left, middle_right, uncle)))));
        assumption();
    }
}

function sized_mirrored_context_double_subtree_before(g: struct rb_node*, p: struct rb_node*, node: struct rb_node*, above: struct rb_node*, nv: int32, pv: int32, gv: int32, far_right: SizedTree, middle_left: SizedTree, middle_right: SizedTree, uncle: SizedTree) -> SizedTree {
    SizedTree::Node(g, above, Color::Black, gv, uncle, SizedTree::Node(p, g, Color::Red, pv, SizedTree::Node(node, p, Color::Red, nv, middle_left, middle_right), far_right))
}

function sized_mirrored_context_double_subtree_after(g: struct rb_node*, p: struct rb_node*, node: struct rb_node*, above: struct rb_node*, far_right: SizedTree, middle_left: SizedTree, middle_right: SizedTree, uncle: SizedTree) -> RbTree {
    RbTree::Node(node, above, Color::Black, RbTree::Node(g, node, Color::Red, sized_shape(uncle), rb_reparent(sized_shape(middle_left), g)), RbTree::Node(p, node, Color::Red, rb_reparent(sized_shape(middle_right), p), sized_shape(far_right)))
}

theorem sized_mirrored_context_double_subtree_matches_insert_fix(g: struct rb_node*, p: struct rb_node*, node: struct rb_node*, above: struct rb_node*, nv: int32, pv: int32, gv: int32, far_right: SizedTree, middle_left: SizedTree, middle_right: SizedTree, uncle: SizedTree) {
    ensures sized_mirrored_context_double_subtree_after(g, p, node, above, far_right, middle_left, middle_right, uncle) == rb_insert_fix_outer_right(rb_insert_fix_inner_right(sized_shape(sized_mirrored_context_double_subtree_before(g, p, node, above, nv, pv, gv, far_right, middle_left, middle_right, uncle)))) by {
        unfold(sized_mirrored_context_double_subtree_before(g, p, node, above, nv, pv, gv, far_right, middle_left, middle_right, uncle));
        unfold(sized_shape(SizedTree::Node(g, above, Color::Black, gv, uncle, SizedTree::Node(p, g, Color::Red, pv, SizedTree::Node(node, p, Color::Red, nv, middle_left, middle_right), far_right))));
        unfold(sized_shape(SizedTree::Node(p, g, Color::Red, pv, SizedTree::Node(node, p, Color::Red, nv, middle_left, middle_right), far_right)));
        unfold(sized_shape(SizedTree::Node(node, p, Color::Red, nv, middle_left, middle_right)));
        unfold(rb_insert_fix_inner_right(RbTree::Node(g, above, Color::Black, sized_shape(uncle), RbTree::Node(p, g, Color::Red, RbTree::Node(node, p, Color::Red, sized_shape(middle_left), sized_shape(middle_right)), sized_shape(far_right)))));
        unfold(rb_rotate_right_at_right(RbTree::Node(g, above, Color::Black, sized_shape(uncle), RbTree::Node(p, g, Color::Red, RbTree::Node(node, p, Color::Red, sized_shape(middle_left), sized_shape(middle_right)), sized_shape(far_right)))));
        unfold(rb_rotate_right(RbTree::Node(p, g, Color::Red, RbTree::Node(node, p, Color::Red, sized_shape(middle_left), sized_shape(middle_right)), sized_shape(far_right))));
        unfold(rb_insert_fix_outer_right(RbTree::Node(g, above, Color::Black, sized_shape(uncle), RbTree::Node(node, g, Color::Red, sized_shape(middle_left), RbTree::Node(p, node, Color::Red, rb_reparent(sized_shape(middle_right), p), sized_shape(far_right))))));
        unfold(rb_rotate_left(RbTree::Node(g, above, Color::Black, sized_shape(uncle), RbTree::Node(node, g, Color::Red, sized_shape(middle_left), RbTree::Node(p, node, Color::Red, rb_reparent(sized_shape(middle_right), p), sized_shape(far_right))))));
        unfold(rb_recolor_left(RbTree::Node(node, above, Color::Red, RbTree::Node(g, node, Color::Black, sized_shape(uncle), rb_reparent(sized_shape(middle_left), g)), RbTree::Node(p, node, Color::Red, rb_reparent(sized_shape(middle_right), p), sized_shape(far_right))), Color::Red));
        unfold(rb_recolor(RbTree::Node(g, node, Color::Black, sized_shape(uncle), rb_reparent(sized_shape(middle_left), g)), Color::Red));
        unfold(rb_recolor(RbTree::Node(node, above, Color::Red, RbTree::Node(g, node, Color::Red, sized_shape(uncle), rb_reparent(sized_shape(middle_left), g)), RbTree::Node(p, node, Color::Red, rb_reparent(sized_shape(middle_right), p), sized_shape(far_right))), Color::Black));
        unfold(sized_mirrored_context_double_subtree_after(g, p, node, above, far_right, middle_left, middle_right, uncle));
        normalize();
    }
}

theorem sized_mirrored_context_double_subtree_preserves_inorder(g: struct rb_node*, p: struct rb_node*, node: struct rb_node*, above: struct rb_node*, nv: int32, pv: int32, gv: int32, far_right: SizedTree, middle_left: SizedTree, middle_right: SizedTree, uncle: SizedTree) {
    ensures rb_inorder(sized_mirrored_context_double_subtree_after(g, p, node, above, far_right, middle_left, middle_right, uncle)) == rb_inorder(sized_shape(sized_mirrored_context_double_subtree_before(g, p, node, above, nv, pv, gv, far_right, middle_left, middle_right, uncle))) by {
        apply(sized_mirrored_context_double_subtree_matches_insert_fix(g, p, node, above, nv, pv, gv, far_right, middle_left, middle_right, uncle));
        rewrite(sized_mirrored_context_double_subtree_after(g, p, node, above, far_right, middle_left, middle_right, uncle) == rb_insert_fix_outer_right(rb_insert_fix_inner_right(sized_shape(sized_mirrored_context_double_subtree_before(g, p, node, above, nv, pv, gv, far_right, middle_left, middle_right, uncle)))));
        apply(rb_insert_fix_outer_right_preserves_inorder(rb_insert_fix_inner_right(sized_shape(sized_mirrored_context_double_subtree_before(g, p, node, above, nv, pv, gv, far_right, middle_left, middle_right, uncle)))));
        apply(rb_insert_fix_inner_right_preserves_inorder(sized_shape(sized_mirrored_context_double_subtree_before(g, p, node, above, nv, pv, gv, far_right, middle_left, middle_right, uncle))));
        rewrite(rb_inorder(rb_insert_fix_outer_right(rb_insert_fix_inner_right(sized_shape(sized_mirrored_context_double_subtree_before(g, p, node, above, nv, pv, gv, far_right, middle_left, middle_right, uncle))))) == rb_inorder(rb_insert_fix_inner_right(sized_shape(sized_mirrored_context_double_subtree_before(g, p, node, above, nv, pv, gv, far_right, middle_left, middle_right, uncle)))));
        assumption();
    }
}
