// Arithmetic and cache validity for an inner rotation with a transferred child.
verifying "rbtree_size_compute.c";
verifying "rbtree_size_copy.c";
import "rbtree_size_valid_value.click";
import "rbtree_size_reparent.click";
import "size_arithmetic.click";

theorem sized_double_middle_bounds(pv: int32, nv: int32, far: SizedTree, middle: SizedTree) {
    requires sized_counts_valid(far) == 1;
    requires sized_counts_valid(middle) == 1;
    requires to_integer(nv) == 1 + to_integer(sized_value(middle));
    requires to_integer(pv) == 1 + to_integer(sized_value(far)) + to_integer(nv);
    ensures defined(pv - 1)
        and 0 <= sized_value(far)
        and 0 <= sized_value(middle)
        and sized_value(middle) <= 2147483646
        and sized_value(far) <= 2147483646 - sized_value(middle) by {
        apply(sized_valid_value_nonnegative(far));
        apply(sized_valid_value_nonnegative(middle));
        apply(click::integer::int32_to_integer_bounds(pv));
        have to_integer(pv) == 2 + to_integer(sized_value(far)) + to_integer(sized_value(middle)) by {
            arithmetic() using {
                to_integer(pv) == 1 + to_integer(sized_value(far)) + to_integer(nv);
                to_integer(nv) == 1 + to_integer(sized_value(middle));
            };
        }
        have to_integer(pv) - to_integer(1) >= -2147483648 by {
            arithmetic() using {
                to_integer(pv) == 2 + to_integer(sized_value(far)) + to_integer(sized_value(middle));
                0 <= to_integer(sized_value(far));
                0 <= to_integer(sized_value(middle));
            };
        }
        have to_integer(pv) - to_integer(1) <= 2147483647 by {
            arithmetic() using { to_integer(pv) <= 2147483647; };
        }
        apply(click::integer::int32_subtract_defined_by_integer_bounds(pv, 1));
        have 1 + to_integer(sized_value(far)) + to_integer(sized_value(middle)) <= 2147483647 by {
            arithmetic() using {
                to_integer(pv) == 2 + to_integer(sized_value(far)) + to_integer(sized_value(middle));
                to_integer(pv) <= 2147483647;
            };
        }
        apply(size_children_fit(sized_value(far), sized_value(middle)));
        simp();
    }
}

theorem sized_double_middle_valid(p: struct rb_node*, node: struct rb_node*, pv: int32,
                                  far: SizedTree, middle: SizedTree) {
    requires sized_counts_valid(far) == 1;
    requires sized_counts_valid(middle) == 1;
    requires defined(pv - 1);
    requires to_integer(pv) == 2 + to_integer(sized_value(far)) + to_integer(sized_value(middle));
    ensures sized_counts_valid(SizedTree::Node(p, node, Color::Red, pv - 1, far,
                sized_recolor(sized_reparent(middle, p), Color::Black))) == 1
        and sized_counts_valid(SizedTree::Node(node, p, Color::Red, pv,
                SizedTree::Node(p, node, Color::Red, pv - 1, far,
                    sized_recolor(sized_reparent(middle, p), Color::Black)), SizedTree::Empty)) == 1 by {
        apply(sized_reparent_observations(middle, p));
        apply(sized_recolor_observations(sized_reparent(middle, p), Color::Black));
        apply(click::integer::int32_subtract_to_integer(pv, 1));
        have to_integer(pv - 1) == 1 + to_integer(sized_value(far))
                + to_integer(sized_value(sized_recolor(sized_reparent(middle, p), Color::Black))) by {
            rewrite(sized_value(sized_recolor(sized_reparent(middle, p), Color::Black)) == sized_value(sized_reparent(middle, p)));
            rewrite(sized_value(sized_reparent(middle, p)) == sized_value(middle));
            arithmetic() using {
                to_integer(pv) == 2 + to_integer(sized_value(far)) + to_integer(sized_value(middle));
                to_integer(pv - 1) == to_integer(pv) - to_integer(1);
            };
        }
        apply(sized_valid_node(p, node, Color::Red, pv - 1, far,
            sized_recolor(sized_reparent(middle, p), Color::Black)));
        unfold(sized_value(SizedTree::Node(p, node, Color::Red, pv - 1, far,
            sized_recolor(sized_reparent(middle, p), Color::Black))));
        unfold(sized_value(SizedTree::Empty));
        unfold(sized_counts_valid(SizedTree::Empty));
        have to_integer(pv) == 1 + to_integer(sized_value(SizedTree::Node(p, node, Color::Red, pv - 1, far,
                    sized_recolor(sized_reparent(middle, p), Color::Black)))) + to_integer(sized_value(SizedTree::Empty)) by {
            rewrite(sized_value(SizedTree::Node(p, node, Color::Red, pv - 1, far,
                sized_recolor(sized_reparent(middle, p), Color::Black))) == pv - 1);
            rewrite(sized_value(SizedTree::Empty) == 0);
            arithmetic() using { to_integer(pv - 1) == to_integer(pv) - to_integer(1); };
        }
        apply(sized_valid_node(node, p, Color::Red, pv,
            SizedTree::Node(p, node, Color::Red, pv - 1, far,
                sized_recolor(sized_reparent(middle, p), Color::Black)), SizedTree::Empty));
        simp();
    }
}

theorem sized_mirrored_double_middle_valid(p: struct rb_node*, node: struct rb_node*, pv: int32,
                                  far: SizedTree, middle: SizedTree) {
    requires sized_counts_valid(far) == 1;
    requires sized_counts_valid(middle) == 1;
    requires defined(pv - 1);
    requires to_integer(pv) == 2 + to_integer(sized_value(far)) + to_integer(sized_value(middle));
    ensures sized_counts_valid(SizedTree::Node(p, node, Color::Red, pv - 1,
                sized_recolor(sized_reparent(middle, p), Color::Black), far)) == 1
        and sized_counts_valid(SizedTree::Node(node, p, Color::Red, pv, SizedTree::Empty,
                SizedTree::Node(p, node, Color::Red, pv - 1,
                    sized_recolor(sized_reparent(middle, p), Color::Black), far))) == 1 by {
        apply(sized_reparent_observations(middle, p));
        apply(sized_recolor_observations(sized_reparent(middle, p), Color::Black));
        apply(click::integer::int32_subtract_to_integer(pv, 1));
        have to_integer(pv - 1) == 1 + to_integer(sized_value(sized_recolor(sized_reparent(middle, p), Color::Black)))
                + to_integer(sized_value(far)) by {
            rewrite(sized_value(sized_recolor(sized_reparent(middle, p), Color::Black)) == sized_value(sized_reparent(middle, p)));
            rewrite(sized_value(sized_reparent(middle, p)) == sized_value(middle));
            arithmetic() using {
                to_integer(pv) == 2 + to_integer(sized_value(far)) + to_integer(sized_value(middle));
                to_integer(pv - 1) == to_integer(pv) - to_integer(1);
            };
        }
        apply(sized_valid_node(p, node, Color::Red, pv - 1,
            sized_recolor(sized_reparent(middle, p), Color::Black), far));
        unfold(sized_value(SizedTree::Node(p, node, Color::Red, pv - 1,
            sized_recolor(sized_reparent(middle, p), Color::Black), far)));
        unfold(sized_value(SizedTree::Empty));
        unfold(sized_counts_valid(SizedTree::Empty));
        have to_integer(pv) == 1 + to_integer(sized_value(SizedTree::Empty))
                + to_integer(sized_value(SizedTree::Node(p, node, Color::Red, pv - 1,
                    sized_recolor(sized_reparent(middle, p), Color::Black), far))) by {
            rewrite(sized_value(SizedTree::Node(p, node, Color::Red, pv - 1,
                sized_recolor(sized_reparent(middle, p), Color::Black), far)) == pv - 1);
            rewrite(sized_value(SizedTree::Empty) == 0);
            arithmetic() using { to_integer(pv - 1) == to_integer(pv) - to_integer(1); };
        }
        apply(sized_valid_node(node, p, Color::Red, pv, SizedTree::Empty,
            SizedTree::Node(p, node, Color::Red, pv - 1,
                sized_recolor(sized_reparent(middle, p), Color::Black), far)));
        simp();
    }
}
