// Complete cached models for both double rotations, independent of C memory.
verifying "rbtree_size_compute.c";
verifying "rbtree_size_copy.c";
import "rbtree_size_double_outer_counts.click";
import "rbtree_size_insert_double_subtree_model.click";

function sized_double_cached_after(g: struct rb_node*, p: struct rb_node*, node: struct rb_node*, above: struct rb_node*, gv: int32, pc: int32, gc: int32, far: SizedTree, ml: SizedTree, mr: SizedTree, uncle: SizedTree) -> SizedTree {
    SizedTree::Node(node, above, Color::Black, gv, SizedTree::Node(p, node, Color::Red, pc, far, sized_reparent(ml, p)), SizedTree::Node(g, node, Color::Red, gc, sized_reparent(mr, g), uncle))
}

theorem sized_double_cached_valid(g: struct rb_node*, p: struct rb_node*, node: struct rb_node*, above: struct rb_node*, gv: int32, pc: int32, gc: int32, far: SizedTree, ml: SizedTree, mr: SizedTree, uncle: SizedTree) {
    requires sized_counts_valid(far) == 1;
    requires sized_counts_valid(ml) == 1;
    requires sized_counts_valid(mr) == 1;
    requires sized_counts_valid(uncle) == 1;
    requires to_integer(pc) == 1 + to_integer(sized_value(far)) + to_integer(sized_value(ml));
    requires to_integer(gc) == 1 + to_integer(sized_value(mr)) + to_integer(sized_value(uncle));
    requires to_integer(gv) == 3 + to_integer(sized_value(far)) + to_integer(sized_value(ml)) + to_integer(sized_value(mr)) + to_integer(sized_value(uncle));
    ensures sized_counts_valid(sized_double_cached_after(g, p, node, above, gv, pc, gc, far, ml, mr, uncle)) == 1 by {
        apply(sized_reparent_observations(ml, p));
        have sized_counts_valid(sized_reparent(ml, p)) == 1 by {
            rewrite(sized_counts_valid(sized_reparent(ml, p)) == sized_counts_valid(ml)); assumption();
        }
        have to_integer(pc) == 1 + to_integer(sized_value(far)) + to_integer(sized_value(sized_reparent(ml, p))) by {
            rewrite(sized_value(sized_reparent(ml, p)) == sized_value(ml));
            solve() using { to_integer(pc) == 1 + to_integer(sized_value(far)) + to_integer(sized_value(ml)); };
        }
        apply(sized_valid_node(p, node, Color::Red, pc, far, sized_reparent(ml, p)));
        unfold(sized_value(SizedTree::Node(p, node, Color::Red, pc, far, sized_reparent(ml, p))));
        have to_integer(gv) == 1 + to_integer(sized_value(SizedTree::Node(p, node, Color::Red, pc, far, sized_reparent(ml, p)))) + to_integer(gc) by {
            rewrite(sized_value(SizedTree::Node(p, node, Color::Red, pc, far, sized_reparent(ml, p))) == pc);
            solve() using {
                to_integer(pc) == 1 + to_integer(sized_value(far)) + to_integer(sized_value(ml));
                to_integer(gc) == 1 + to_integer(sized_value(mr)) + to_integer(sized_value(uncle));
                to_integer(gv) == 3 + to_integer(sized_value(far)) + to_integer(sized_value(ml)) + to_integer(sized_value(mr)) + to_integer(sized_value(uncle));
            };
        }
        apply(sized_double_outer_right_valid(g, node, above, gv, gc, SizedTree::Node(p, node, Color::Red, pc, far, sized_reparent(ml, p)), mr, uncle));
        unfold(sized_double_cached_after(g, p, node, above, gv, pc, gc, far, ml, mr, uncle));
        assumption();
    }
}

theorem sized_double_cached_shape(g: struct rb_node*, p: struct rb_node*, node: struct rb_node*, above: struct rb_node*, gv: int32, pc: int32, gc: int32, far: SizedTree, ml: SizedTree, mr: SizedTree, uncle: SizedTree) {
    ensures sized_shape(sized_double_cached_after(g, p, node, above, gv, pc, gc, far, ml, mr, uncle)) == sized_context_double_subtree_after(g, p, node, above, far, ml, mr, uncle) by {
        apply(sized_reparent_observations(ml, p));
        apply(sized_reparent_observations(mr, g));
        unfold(sized_double_cached_after(g, p, node, above, gv, pc, gc, far, ml, mr, uncle));
        unfold(sized_shape(SizedTree::Node(node, above, Color::Black, gv, SizedTree::Node(p, node, Color::Red, pc, far, sized_reparent(ml, p)), SizedTree::Node(g, node, Color::Red, gc, sized_reparent(mr, g), uncle))));
        unfold(sized_shape(SizedTree::Node(p, node, Color::Red, pc, far, sized_reparent(ml, p))));
        unfold(sized_shape(SizedTree::Node(g, node, Color::Red, gc, sized_reparent(mr, g), uncle)));
        unfold(sized_context_double_subtree_after(g, p, node, above, far, ml, mr, uncle));
        rewrite(sized_shape(sized_reparent(ml, p)) == rb_reparent(sized_shape(ml), p));
        rewrite(sized_shape(sized_reparent(mr, g)) == rb_reparent(sized_shape(mr), g));
        normalize();
    }
}

theorem sized_double_cached_inorder(g: struct rb_node*, p: struct rb_node*, node: struct rb_node*, above: struct rb_node*, gv: int32, pc: int32, gc: int32, far: SizedTree, ml: SizedTree, mr: SizedTree, uncle: SizedTree, nv: int32, pv: int32) {
    ensures rb_inorder(sized_shape(sized_double_cached_after(g, p, node, above, gv, pc, gc, far, ml, mr, uncle))) == rb_inorder(sized_shape(sized_context_double_subtree_before(g, p, node, above, nv, pv, gv, far, ml, mr, uncle))) by {
        apply(sized_double_cached_shape(g, p, node, above, gv, pc, gc, far, ml, mr, uncle));
        rewrite(sized_shape(sized_double_cached_after(g, p, node, above, gv, pc, gc, far, ml, mr, uncle)) == sized_context_double_subtree_after(g, p, node, above, far, ml, mr, uncle));
        apply(sized_context_double_subtree_preserves_inorder(g, p, node, above, nv, pv, gv, far, ml, mr, uncle));
        assumption();
    }
}

function sized_mirrored_double_cached_after(g: struct rb_node*, p: struct rb_node*, node: struct rb_node*, above: struct rb_node*, gv: int32, pc: int32, gc: int32, far: SizedTree, ml: SizedTree, mr: SizedTree, uncle: SizedTree) -> SizedTree {
    SizedTree::Node(node, above, Color::Black, gv, SizedTree::Node(g, node, Color::Red, gc, uncle, sized_reparent(ml, g)), SizedTree::Node(p, node, Color::Red, pc, sized_reparent(mr, p), far))
}

theorem sized_mirrored_double_cached_valid(g: struct rb_node*, p: struct rb_node*, node: struct rb_node*, above: struct rb_node*, gv: int32, pc: int32, gc: int32, far: SizedTree, ml: SizedTree, mr: SizedTree, uncle: SizedTree) {
    requires sized_counts_valid(far) == 1;
    requires sized_counts_valid(ml) == 1;
    requires sized_counts_valid(mr) == 1;
    requires sized_counts_valid(uncle) == 1;
    requires to_integer(pc) == 1 + to_integer(sized_value(far)) + to_integer(sized_value(mr));
    requires to_integer(gc) == 1 + to_integer(sized_value(ml)) + to_integer(sized_value(uncle));
    requires to_integer(gv) == 3 + to_integer(sized_value(far)) + to_integer(sized_value(ml)) + to_integer(sized_value(mr)) + to_integer(sized_value(uncle));
    ensures sized_counts_valid(sized_mirrored_double_cached_after(g, p, node, above, gv, pc, gc, far, ml, mr, uncle)) == 1 by {
        apply(sized_reparent_observations(mr, p));
        have sized_counts_valid(sized_reparent(mr, p)) == 1 by {
            rewrite(sized_counts_valid(sized_reparent(mr, p)) == sized_counts_valid(mr)); assumption();
        }
        have to_integer(pc) == 1 + to_integer(sized_value(sized_reparent(mr, p))) + to_integer(sized_value(far)) by {
            rewrite(sized_value(sized_reparent(mr, p)) == sized_value(mr));
            solve() using { to_integer(pc) == 1 + to_integer(sized_value(far)) + to_integer(sized_value(mr)); };
        }
        apply(sized_valid_node(p, node, Color::Red, pc, sized_reparent(mr, p), far));
        unfold(sized_value(SizedTree::Node(p, node, Color::Red, pc, sized_reparent(mr, p), far)));
        have to_integer(gv) == 1 + to_integer(sized_value(SizedTree::Node(p, node, Color::Red, pc, sized_reparent(mr, p), far))) + to_integer(gc) by {
            rewrite(sized_value(SizedTree::Node(p, node, Color::Red, pc, sized_reparent(mr, p), far)) == pc);
            solve() using {
                to_integer(pc) == 1 + to_integer(sized_value(far)) + to_integer(sized_value(mr));
                to_integer(gc) == 1 + to_integer(sized_value(ml)) + to_integer(sized_value(uncle));
                to_integer(gv) == 3 + to_integer(sized_value(far)) + to_integer(sized_value(ml)) + to_integer(sized_value(mr)) + to_integer(sized_value(uncle));
            };
        }
        apply(sized_double_outer_left_valid(g, node, above, gv, gc, SizedTree::Node(p, node, Color::Red, pc, sized_reparent(mr, p), far), ml, uncle));
        unfold(sized_mirrored_double_cached_after(g, p, node, above, gv, pc, gc, far, ml, mr, uncle));
        assumption();
    }
}

theorem sized_mirrored_double_cached_shape(g: struct rb_node*, p: struct rb_node*, node: struct rb_node*, above: struct rb_node*, gv: int32, pc: int32, gc: int32, far: SizedTree, ml: SizedTree, mr: SizedTree, uncle: SizedTree) {
    ensures sized_shape(sized_mirrored_double_cached_after(g, p, node, above, gv, pc, gc, far, ml, mr, uncle)) == sized_mirrored_context_double_subtree_after(g, p, node, above, far, ml, mr, uncle) by {
        apply(sized_reparent_observations(mr, p));
        apply(sized_reparent_observations(ml, g));
        unfold(sized_mirrored_double_cached_after(g, p, node, above, gv, pc, gc, far, ml, mr, uncle));
        unfold(sized_shape(SizedTree::Node(node, above, Color::Black, gv, SizedTree::Node(g, node, Color::Red, gc, uncle, sized_reparent(ml, g)), SizedTree::Node(p, node, Color::Red, pc, sized_reparent(mr, p), far))));
        unfold(sized_shape(SizedTree::Node(p, node, Color::Red, pc, sized_reparent(mr, p), far)));
        unfold(sized_shape(SizedTree::Node(g, node, Color::Red, gc, uncle, sized_reparent(ml, g))));
        unfold(sized_mirrored_context_double_subtree_after(g, p, node, above, far, ml, mr, uncle));
        rewrite(sized_shape(sized_reparent(mr, p)) == rb_reparent(sized_shape(mr), p));
        rewrite(sized_shape(sized_reparent(ml, g)) == rb_reparent(sized_shape(ml), g));
        normalize();
    }
}

theorem sized_mirrored_double_cached_inorder(g: struct rb_node*, p: struct rb_node*, node: struct rb_node*, above: struct rb_node*, gv: int32, pc: int32, gc: int32, far: SizedTree, ml: SizedTree, mr: SizedTree, uncle: SizedTree, nv: int32, pv: int32) {
    ensures rb_inorder(sized_shape(sized_mirrored_double_cached_after(g, p, node, above, gv, pc, gc, far, ml, mr, uncle))) == rb_inorder(sized_shape(sized_mirrored_context_double_subtree_before(g, p, node, above, nv, pv, gv, far, ml, mr, uncle))) by {
        apply(sized_mirrored_double_cached_shape(g, p, node, above, gv, pc, gc, far, ml, mr, uncle));
        rewrite(sized_shape(sized_mirrored_double_cached_after(g, p, node, above, gv, pc, gc, far, ml, mr, uncle)) == sized_mirrored_context_double_subtree_after(g, p, node, above, far, ml, mr, uncle));
        apply(sized_mirrored_context_double_subtree_preserves_inorder(g, p, node, above, nv, pv, gv, far, ml, mr, uncle));
        assumption();
    }
}
