// Derive the complete post-rotation cache invariant from the input invariant.
verifying "rbtree_size_compute.c";
verifying "rbtree_size_copy.c";
import "rbtree_size_double_cached_model.click";

theorem sized_double_preserves_counts(g: struct rb_node*, p: struct rb_node*, node: struct rb_node*, above: struct rb_node*,
    nv: int32, pv: int32, gv: int32, pc: int32, gc: int32,
    far: SizedTree, ml: SizedTree, mr: SizedTree, uncle: SizedTree) {
    requires sized_counts_valid(sized_context_double_subtree_before(g, p, node, above, nv, pv, gv, far, ml, mr, uncle)) == 1;
    requires to_integer(pc) == 1 + to_integer(sized_value(far)) + to_integer(sized_value(ml));
    requires to_integer(gc) == 1 + to_integer(sized_value(mr)) + to_integer(sized_value(uncle));
    ensures sized_counts_valid(sized_double_cached_after(g, p, node, above, gv, pc, gc, far, ml, mr, uncle)) == 1 by {
        unfold(sized_context_double_subtree_before(g, p, node, above, nv, pv, gv, far, ml, mr, uncle));
        have sized_counts_valid(SizedTree::Node(g, above, Color::Black, gv, SizedTree::Node(p, g, Color::Red, pv, far, SizedTree::Node(node, p, Color::Red, nv, ml, mr)), uncle)) == 1 by {
            rewrite(SizedTree::Node(g, above, Color::Black, gv, SizedTree::Node(p, g, Color::Red, pv, far, SizedTree::Node(node, p, Color::Red, nv, ml, mr)), uncle) == sized_context_double_subtree_before(g, p, node, above, nv, pv, gv, far, ml, mr, uncle)); assumption();
        }
        apply(sized_valid_parts(g, above, Color::Black, gv, SizedTree::Node(p, g, Color::Red, pv, far, SizedTree::Node(node, p, Color::Red, nv, ml, mr)), uncle));
        apply(sized_valid_parts(p, g, Color::Red, pv, far, SizedTree::Node(node, p, Color::Red, nv, ml, mr)));
        apply(sized_valid_parts(node, p, Color::Red, nv, ml, mr));
        unfold(sized_value(SizedTree::Node(p, g, Color::Red, pv, far, SizedTree::Node(node, p, Color::Red, nv, ml, mr))));
        unfold(sized_value(SizedTree::Node(node, p, Color::Red, nv, ml, mr)));
        have to_integer(pv) == 1 + to_integer(sized_value(far)) + to_integer(nv) by {
            rewrite(nv == sized_value(SizedTree::Node(node, p, Color::Red, nv, ml, mr)));
            solve() using { to_integer(pv) == 1 + to_integer(sized_value(far)) + to_integer(sized_value(SizedTree::Node(node, p, Color::Red, nv, ml, mr))); };
        }
        have to_integer(gv) == 1 + to_integer(pv) + to_integer(sized_value(uncle)) by {
            rewrite(pv == sized_value(SizedTree::Node(p, g, Color::Red, pv, far, SizedTree::Node(node, p, Color::Red, nv, ml, mr))));
            solve() using { to_integer(gv) == 1 + to_integer(sized_value(SizedTree::Node(p, g, Color::Red, pv, far, SizedTree::Node(node, p, Color::Red, nv, ml, mr)))) + to_integer(sized_value(uncle)); };
        }
        have to_integer(gv) == 3 + to_integer(sized_value(far)) + to_integer(sized_value(ml)) + to_integer(sized_value(mr)) + to_integer(sized_value(uncle)) by {
            solve() using {
                to_integer(nv) == 1 + to_integer(sized_value(ml)) + to_integer(sized_value(mr));
                to_integer(pv) == 1 + to_integer(sized_value(far)) + to_integer(nv);
                to_integer(gv) == 1 + to_integer(pv) + to_integer(sized_value(uncle));
            };
        }
        apply(sized_double_cached_valid(g, p, node, above, gv, pc, gc, far, ml, mr, uncle));
        assumption();
    }
}

theorem sized_mirrored_double_preserves_counts(g: struct rb_node*, p: struct rb_node*, node: struct rb_node*, above: struct rb_node*,
    nv: int32, pv: int32, gv: int32, pc: int32, gc: int32,
    far: SizedTree, ml: SizedTree, mr: SizedTree, uncle: SizedTree) {
    requires sized_counts_valid(sized_mirrored_context_double_subtree_before(g, p, node, above, nv, pv, gv, far, ml, mr, uncle)) == 1;
    requires to_integer(pc) == 1 + to_integer(sized_value(far)) + to_integer(sized_value(mr));
    requires to_integer(gc) == 1 + to_integer(sized_value(ml)) + to_integer(sized_value(uncle));
    ensures sized_counts_valid(sized_mirrored_double_cached_after(g, p, node, above, gv, pc, gc, far, ml, mr, uncle)) == 1 by {
        unfold(sized_mirrored_context_double_subtree_before(g, p, node, above, nv, pv, gv, far, ml, mr, uncle));
        have sized_counts_valid(SizedTree::Node(g, above, Color::Black, gv, uncle, SizedTree::Node(p, g, Color::Red, pv, SizedTree::Node(node, p, Color::Red, nv, ml, mr), far))) == 1 by {
            rewrite(SizedTree::Node(g, above, Color::Black, gv, uncle, SizedTree::Node(p, g, Color::Red, pv, SizedTree::Node(node, p, Color::Red, nv, ml, mr), far)) == sized_mirrored_context_double_subtree_before(g, p, node, above, nv, pv, gv, far, ml, mr, uncle)); assumption();
        }
        apply(sized_valid_parts(g, above, Color::Black, gv, uncle, SizedTree::Node(p, g, Color::Red, pv, SizedTree::Node(node, p, Color::Red, nv, ml, mr), far)));
        apply(sized_valid_parts(p, g, Color::Red, pv, SizedTree::Node(node, p, Color::Red, nv, ml, mr), far));
        apply(sized_valid_parts(node, p, Color::Red, nv, ml, mr));
        unfold(sized_value(SizedTree::Node(p, g, Color::Red, pv, SizedTree::Node(node, p, Color::Red, nv, ml, mr), far)));
        unfold(sized_value(SizedTree::Node(node, p, Color::Red, nv, ml, mr)));
        have to_integer(pv) == 1 + to_integer(sized_value(far)) + to_integer(nv) by {
            rewrite(nv == sized_value(SizedTree::Node(node, p, Color::Red, nv, ml, mr)));
            solve() using { to_integer(pv) == 1 + to_integer(sized_value(SizedTree::Node(node, p, Color::Red, nv, ml, mr))) + to_integer(sized_value(far)); };
        }
        have to_integer(gv) == 1 + to_integer(pv) + to_integer(sized_value(uncle)) by {
            rewrite(pv == sized_value(SizedTree::Node(p, g, Color::Red, pv, SizedTree::Node(node, p, Color::Red, nv, ml, mr), far)));
            solve() using { to_integer(gv) == 1 + to_integer(sized_value(uncle)) + to_integer(sized_value(SizedTree::Node(p, g, Color::Red, pv, SizedTree::Node(node, p, Color::Red, nv, ml, mr), far))); };
        }
        have to_integer(gv) == 3 + to_integer(sized_value(far)) + to_integer(sized_value(ml)) + to_integer(sized_value(mr)) + to_integer(sized_value(uncle)) by {
            solve() using {
                to_integer(nv) == 1 + to_integer(sized_value(ml)) + to_integer(sized_value(mr));
                to_integer(pv) == 1 + to_integer(sized_value(far)) + to_integer(nv);
                to_integer(gv) == 1 + to_integer(pv) + to_integer(sized_value(uncle));
            };
        }
        apply(sized_mirrored_double_cached_valid(g, p, node, above, gv, pc, gc, far, ml, mr, uncle));
        assumption();
    }
}
