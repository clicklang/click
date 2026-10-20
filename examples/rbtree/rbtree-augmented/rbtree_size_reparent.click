arithmetic "integer";

// Reparenting a subtree root changes neither its caches nor its children.
verifying "rbtree_size_compute.c";
verifying "rbtree_size_copy.c";
import "rbtree_size_recolor.click";

function sized_reparent(tree: SizedTree, parent: struct rb_node*) -> SizedTree {
    match tree {
        SizedTree::Empty => SizedTree::Empty,
        SizedTree::Node(node, before, color, value, left, right) =>
            SizedTree::Node(node, parent, color, value, left, right),
    }
}

theorem sized_reparent_observations(tree: SizedTree, parent: struct rb_node*) {
    ensures sized_value(sized_reparent(tree, parent)) == sized_value(tree) by {
        match tree {
            SizedTree::Empty => {
                rewrite(tree == SizedTree::Empty);
                unfold(sized_reparent(SizedTree::Empty, parent));
                unfold(sized_value(SizedTree::Empty));
                normalize();
            },
            SizedTree::Node(node, before, color, value, left, right) => {
                rewrite(tree == SizedTree::Node(node, before, color, value, left, right));
                unfold(sized_reparent(SizedTree::Node(node, before, color, value, left, right), parent));
                unfold(sized_value(SizedTree::Node(node, parent, color, value, left, right)));
                unfold(sized_value(SizedTree::Node(node, before, color, value, left, right)));
                normalize();
            },
        }
    }
    ensures sized_counts_valid(sized_reparent(tree, parent)) == sized_counts_valid(tree) by {
        match tree {
            SizedTree::Empty => {
                rewrite(tree == SizedTree::Empty);
                unfold(sized_reparent(SizedTree::Empty, parent));
                unfold(sized_counts_valid(SizedTree::Empty));
                normalize();
            },
            SizedTree::Node(node, before, color, value, left, right) => {
                rewrite(tree == SizedTree::Node(node, before, color, value, left, right));
                unfold(sized_reparent(SizedTree::Node(node, before, color, value, left, right), parent));
                unfold(sized_counts_valid(SizedTree::Node(node, parent, color, value, left, right)));
                unfold(sized_counts_valid(SizedTree::Node(node, before, color, value, left, right)));
                normalize();
            },
        }
    }
    ensures sized_parent_is(sized_reparent(tree, parent), parent) == 1 by {
        match tree {
            SizedTree::Empty => {
                rewrite(tree == SizedTree::Empty);
                unfold(sized_reparent(SizedTree::Empty, parent));
                unfold(sized_parent_is(SizedTree::Empty, parent));
                normalize();
            },
            SizedTree::Node(node, before, color, value, left, right) => {
                rewrite(tree == SizedTree::Node(node, before, color, value, left, right));
                unfold(sized_reparent(SizedTree::Node(node, before, color, value, left, right), parent));
                unfold(sized_parent_is(SizedTree::Node(node, parent, color, value, left, right), parent));
                normalize();
            },
        }
    }
    ensures sized_shape(sized_reparent(tree, parent)) == rb_reparent(sized_shape(tree), parent) by {
        match tree {
            SizedTree::Empty => {
                rewrite(tree == SizedTree::Empty);
                unfold(sized_reparent(SizedTree::Empty, parent));
                unfold(sized_shape(SizedTree::Empty));
                unfold(rb_reparent(RbTree::Empty, parent));
                normalize();
            },
            SizedTree::Node(node, before, color, value, left, right) => {
                rewrite(tree == SizedTree::Node(node, before, color, value, left, right));
                unfold(sized_reparent(SizedTree::Node(node, before, color, value, left, right), parent));
                unfold(sized_shape(SizedTree::Node(node, parent, color, value, left, right)));
                unfold(sized_shape(SizedTree::Node(node, before, color, value, left, right)));
                unfold(rb_reparent(RbTree::Node(node, before, color, sized_shape(left), sized_shape(right)), parent));
                normalize();
            },
        }
    }
}
