arithmetic "integer";

// Recoloring changes no cached subtree count.
verifying "rbtree_size_compute.c";
verifying "rbtree_size_copy.c";
import "rbtree_size_metadata.click";

function sized_recolor(tree: SizedTree, color: Color) -> SizedTree {
    match tree {
        SizedTree::Empty => SizedTree::Empty,
        SizedTree::Node(node, parent, before, value, left, right) =>
            SizedTree::Node(node, parent, color, value, left, right),
    }
}

theorem sized_recolor_observations(tree: SizedTree, shade: Color) {
    ensures sized_value(sized_recolor(tree, shade)) == sized_value(tree) by {
        match tree {
            SizedTree::Empty => {
                rewrite(tree == SizedTree::Empty);
                unfold(sized_recolor(SizedTree::Empty, shade)); normalize();
            },
            SizedTree::Node(node, parent, before, value, left, right) => {
                rewrite(tree == SizedTree::Node(node, parent, before, value, left, right));
                unfold(sized_recolor(SizedTree::Node(node, parent, before, value, left, right), shade));
                unfold(sized_value(SizedTree::Node(node, parent, shade, value, left, right)));
                unfold(sized_value(SizedTree::Node(node, parent, before, value, left, right))); normalize();
            },
        }
    }
    ensures sized_counts_valid(sized_recolor(tree, shade)) == sized_counts_valid(tree) by {
        match tree {
            SizedTree::Empty => {
                rewrite(tree == SizedTree::Empty);
                unfold(sized_recolor(SizedTree::Empty, shade)); normalize();
            },
            SizedTree::Node(node, parent, before, value, left, right) => {
                rewrite(tree == SizedTree::Node(node, parent, before, value, left, right));
                unfold(sized_recolor(SizedTree::Node(node, parent, before, value, left, right), shade));
                unfold(sized_counts_valid(SizedTree::Node(node, parent, shade, value, left, right)));
                unfold(sized_counts_valid(SizedTree::Node(node, parent, before, value, left, right))); normalize();
            },
        }
    }
    ensures sized_shape(sized_recolor(tree, shade)) == rb_recolor(sized_shape(tree), shade) by {
        match tree {
            SizedTree::Empty => {
                rewrite(tree == SizedTree::Empty);
                unfold(sized_recolor(SizedTree::Empty, shade)); unfold(sized_shape(SizedTree::Empty));
                unfold(rb_recolor(RbTree::Empty, shade)); normalize();
            },
            SizedTree::Node(node, parent, before, value, left, right) => {
                rewrite(tree == SizedTree::Node(node, parent, before, value, left, right));
                unfold(sized_recolor(SizedTree::Node(node, parent, before, value, left, right), shade));
                unfold(sized_shape(SizedTree::Node(node, parent, shade, value, left, right)));
                unfold(sized_shape(SizedTree::Node(node, parent, before, value, left, right)));
                unfold(rb_recolor(RbTree::Node(node, parent, before, sized_shape(left), sized_shape(right)), shade)); normalize();
            },
        }
    }
}

function sized_insert_fix_recolor(tree: SizedTree) -> SizedTree {
    match tree {
        SizedTree::Empty => SizedTree::Empty,
        SizedTree::Node(node, parent, before, value, left, right) =>
            SizedTree::Node(node, parent, Color::Red, value,
                sized_recolor(left, Color::Black), sized_recolor(right, Color::Black)),
    }
}

theorem sized_insert_fix_recolor_observations(tree: SizedTree) {
    ensures sized_value(sized_insert_fix_recolor(tree)) == sized_value(tree) by {
        match tree {
            SizedTree::Empty => {
                rewrite(tree == SizedTree::Empty);
                unfold(sized_insert_fix_recolor(SizedTree::Empty)); normalize();
            },
            SizedTree::Node(node, parent, before, value, left, right) => {
                rewrite(tree == SizedTree::Node(node, parent, before, value, left, right));
                unfold(sized_insert_fix_recolor(SizedTree::Node(node, parent, before, value, left, right)));
                unfold(sized_value(SizedTree::Node(node, parent, Color::Red, value, sized_recolor(left, Color::Black), sized_recolor(right, Color::Black))));
                unfold(sized_value(SizedTree::Node(node, parent, before, value, left, right))); normalize();
            },
        }
    }
    ensures sized_counts_valid(sized_insert_fix_recolor(tree)) == sized_counts_valid(tree) by {
        match tree {
            SizedTree::Empty => {
                rewrite(tree == SizedTree::Empty);
                unfold(sized_insert_fix_recolor(SizedTree::Empty)); normalize();
            },
            SizedTree::Node(node, parent, before, value, left, right) => {
                apply(sized_recolor_observations(left, Color::Black));
                apply(sized_recolor_observations(right, Color::Black));
                rewrite(tree == SizedTree::Node(node, parent, before, value, left, right));
                unfold(sized_insert_fix_recolor(SizedTree::Node(node, parent, before, value, left, right)));
                unfold(sized_counts_valid(SizedTree::Node(node, parent, Color::Red, value, sized_recolor(left, Color::Black), sized_recolor(right, Color::Black))));
                unfold(sized_counts_valid(SizedTree::Node(node, parent, before, value, left, right)));
                rewrite(sized_value(sized_recolor(left, Color::Black)) == sized_value(left));
                rewrite(sized_value(sized_recolor(right, Color::Black)) == sized_value(right));
                rewrite(sized_counts_valid(sized_recolor(left, Color::Black)) == sized_counts_valid(left));
                rewrite(sized_counts_valid(sized_recolor(right, Color::Black)) == sized_counts_valid(right)); normalize();
            },
        }
    }
    ensures sized_shape(sized_insert_fix_recolor(tree)) == rb_insert_fix_recolor(sized_shape(tree)) by {
        match tree {
            SizedTree::Empty => {
                rewrite(tree == SizedTree::Empty);
                unfold(sized_insert_fix_recolor(SizedTree::Empty)); unfold(sized_shape(SizedTree::Empty));
                unfold(rb_insert_fix_recolor(RbTree::Empty));
                unfold(rb_recolor_right(RbTree::Empty, Color::Black));
                unfold(rb_recolor_left(RbTree::Empty, Color::Black));
                unfold(rb_recolor(RbTree::Empty, Color::Red)); normalize();
            },
            SizedTree::Node(node, parent, before, value, left, right) => {
                apply(sized_recolor_observations(left, Color::Black));
                apply(sized_recolor_observations(right, Color::Black));
                rewrite(tree == SizedTree::Node(node, parent, before, value, left, right));
                unfold(sized_insert_fix_recolor(SizedTree::Node(node, parent, before, value, left, right)));
                unfold(sized_shape(SizedTree::Node(node, parent, Color::Red, value, sized_recolor(left, Color::Black), sized_recolor(right, Color::Black))));
                unfold(sized_shape(SizedTree::Node(node, parent, before, value, left, right)));
                unfold(rb_insert_fix_recolor(RbTree::Node(node, parent, before, sized_shape(left), sized_shape(right))));
                unfold(rb_recolor_right(RbTree::Node(node, parent, before, sized_shape(left), sized_shape(right)), Color::Black));
                unfold(rb_recolor_left(RbTree::Node(node, parent, before, sized_shape(left), rb_recolor(sized_shape(right), Color::Black)), Color::Black));
                unfold(rb_recolor(RbTree::Node(node, parent, before, rb_recolor(sized_shape(left), Color::Black), rb_recolor(sized_shape(right), Color::Black)), Color::Red));
                rewrite(sized_shape(sized_recolor(left, Color::Black)) == rb_recolor(sized_shape(left), Color::Black));
                rewrite(sized_shape(sized_recolor(right, Color::Black)) == rb_recolor(sized_shape(right), Color::Black)); normalize();
            },
        }
    }
}
