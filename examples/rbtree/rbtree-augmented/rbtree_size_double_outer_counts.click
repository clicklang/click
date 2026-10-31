// Second-callback counts for double rotations with arbitrary retained subtrees.
verifying "rbtree_size_compute.c";
verifying "rbtree_size_copy.c";
import "rbtree_size_double_subtrees_counts.click";

// Outer right rotation: repaired stays left of the promoted root.
theorem sized_double_outer_right_valid(g: struct rb_node*, node: struct rb_node*, above: struct rb_node*,
                                       gv: int32, demoted: int32, repaired: SizedTree, moved: SizedTree, uncle: SizedTree) {
    requires sized_counts_valid(repaired) == 1;
    requires sized_counts_valid(moved) == 1;
    requires sized_counts_valid(uncle) == 1;
    requires to_integer(demoted) == 1 + to_integer(sized_value(moved)) + to_integer(sized_value(uncle));
    requires to_integer(gv) == 1 + to_integer(sized_value(repaired)) + to_integer(demoted);
    ensures sized_counts_valid(SizedTree::Node(g, node, Color::Red, demoted, sized_reparent(moved, g), uncle)) == 1
        and sized_counts_valid(SizedTree::Node(node, above, Color::Black, gv, repaired,
            SizedTree::Node(g, node, Color::Red, demoted, sized_reparent(moved, g), uncle))) == 1 by {
        apply(sized_reparent_observations(moved, g));
        have sized_counts_valid(sized_reparent(moved, g)) == 1 by {
            rewrite(sized_counts_valid(sized_reparent(moved, g)) == sized_counts_valid(moved)); assumption();
        }
        have to_integer(demoted) == 1 + to_integer(sized_value(sized_reparent(moved, g))) + to_integer(sized_value(uncle)) by {
            rewrite(sized_value(sized_reparent(moved, g)) == sized_value(moved)); assumption();
        }
        apply(sized_valid_node(g, node, Color::Red, demoted, sized_reparent(moved, g), uncle));
        unfold(sized_value(SizedTree::Node(g, node, Color::Red, demoted, sized_reparent(moved, g), uncle)));
        have to_integer(gv) == 1 + to_integer(sized_value(repaired))
                + to_integer(sized_value(SizedTree::Node(g, node, Color::Red, demoted, sized_reparent(moved, g), uncle))) by {
            rewrite(sized_value(SizedTree::Node(g, node, Color::Red, demoted, sized_reparent(moved, g), uncle)) == demoted); assumption();
        }
        apply(sized_valid_node(node, above, Color::Black, gv, repaired,
            SizedTree::Node(g, node, Color::Red, demoted, sized_reparent(moved, g), uncle)));
        assumption();
    }
}

// Outer left rotation: repaired stays right of the promoted root.
theorem sized_double_outer_left_valid(g: struct rb_node*, node: struct rb_node*, above: struct rb_node*,
                                      gv: int32, demoted: int32, repaired: SizedTree, moved: SizedTree, uncle: SizedTree) {
    requires sized_counts_valid(repaired) == 1;
    requires sized_counts_valid(moved) == 1;
    requires sized_counts_valid(uncle) == 1;
    requires to_integer(demoted) == 1 + to_integer(sized_value(moved)) + to_integer(sized_value(uncle));
    requires to_integer(gv) == 1 + to_integer(sized_value(repaired)) + to_integer(demoted);
    ensures sized_counts_valid(SizedTree::Node(g, node, Color::Red, demoted, uncle, sized_reparent(moved, g))) == 1
        and sized_counts_valid(SizedTree::Node(node, above, Color::Black, gv,
            SizedTree::Node(g, node, Color::Red, demoted, uncle, sized_reparent(moved, g)), repaired)) == 1 by {
        apply(sized_reparent_observations(moved, g));
        have sized_counts_valid(sized_reparent(moved, g)) == 1 by {
            rewrite(sized_counts_valid(sized_reparent(moved, g)) == sized_counts_valid(moved)); assumption();
        }
        have to_integer(demoted) == 1 + to_integer(sized_value(uncle)) + to_integer(sized_value(moved)) by {
            solve() using { to_integer(demoted) == 1 + to_integer(sized_value(moved)) + to_integer(sized_value(uncle)); };
        }
        have to_integer(demoted) == 1 + to_integer(sized_value(uncle)) + to_integer(sized_value(sized_reparent(moved, g))) by {
            rewrite(sized_value(sized_reparent(moved, g)) == sized_value(moved)); assumption();
        }
        apply(sized_valid_node(g, node, Color::Red, demoted, uncle, sized_reparent(moved, g)));
        unfold(sized_value(SizedTree::Node(g, node, Color::Red, demoted, uncle, sized_reparent(moved, g))));
        have to_integer(gv) == 1 + to_integer(demoted) + to_integer(sized_value(repaired)) by {
            solve() using { to_integer(gv) == 1 + to_integer(sized_value(repaired)) + to_integer(demoted); };
        }
        have to_integer(gv) == 1 + to_integer(sized_value(SizedTree::Node(g, node, Color::Red, demoted, uncle, sized_reparent(moved, g))))
                + to_integer(sized_value(repaired)) by {
            rewrite(sized_value(SizedTree::Node(g, node, Color::Red, demoted, uncle, sized_reparent(moved, g))) == demoted); assumption();
        }
        apply(sized_valid_node(node, above, Color::Black, gv,
            SizedTree::Node(g, node, Color::Red, demoted, uncle, sized_reparent(moved, g)), repaired));
        assumption();
    }
}
