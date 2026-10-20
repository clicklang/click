arithmetic "integer";

// Read a valid cached count without opening ownership or walking C memory.
verifying "rbtree_size_compute.c";
verifying "rbtree_size_copy.c";
import "rbtree_size_metadata.click";

theorem sized_valid_node(identity: struct rb_node*, parent: struct rb_node*, color: Color,
                         value: int32, left: SizedTree, right: SizedTree) {
    requires sized_counts_valid(left) == 1;
    requires sized_counts_valid(right) == 1;
    requires to_integer(value) == 1 + to_integer(sized_value(left)) + to_integer(sized_value(right));
    ensures sized_counts_valid(SizedTree::Node(identity, parent, color, value, left, right)) == 1 by {
        unfold(sized_counts_valid(SizedTree::Node(identity, parent, color, value, left, right)));
        rewrite(to_integer(value) == 1 + to_integer(sized_value(left)) + to_integer(sized_value(right)));
        rewrite(sized_counts_valid(left) == 1);
        rewrite(sized_counts_valid(right) == 1);
        normalize();
    }
}

theorem sized_valid_value_matches_size(tree: SizedTree) {
    requires sized_counts_valid(tree) == 1;
    ensures to_integer(sized_value(tree)) == rb_subtree_size(sized_shape(tree)) by {
        induct(tree) as ih {
            SizedTree::Empty => {
                unfold(sized_value(SizedTree::Empty));
                unfold(sized_shape(SizedTree::Empty));
                unfold(rb_subtree_size(RbTree::Empty));
                normalize();
            },
            SizedTree::Node(identity, parent, color, value, left, right) => {
                apply(sized_valid_parts(identity, parent, color, value, left, right));
                apply(ih(left)) using { sized_counts_valid(left) == 1; };
                apply(ih(right)) using { sized_counts_valid(right) == 1; };
                unfold(sized_value(SizedTree::Node(identity, parent, color, value, left, right)));
                unfold(sized_shape(SizedTree::Node(identity, parent, color, value, left, right)));
                unfold(rb_subtree_size(RbTree::Node(identity, parent, color, sized_shape(left), sized_shape(right))));
                arithmetic() using {
                    to_integer(value) == 1 + to_integer(sized_value(left)) + to_integer(sized_value(right));
                    to_integer(sized_value(left)) == rb_subtree_size(sized_shape(left));
                    to_integer(sized_value(right)) == rb_subtree_size(sized_shape(right));
                };
            },
        }
    }
}

theorem sized_valid_value_nonnegative(tree: SizedTree) {
    requires sized_counts_valid(tree) == 1;
    ensures 0 <= to_integer(sized_value(tree)) by {
        apply(sized_valid_value_matches_size(tree));
        apply(rb_subtree_size_nonnegative(sized_shape(tree)));
        arithmetic() using {
            to_integer(sized_value(tree)) == rb_subtree_size(sized_shape(tree));
            rb_subtree_size(sized_shape(tree)) >= 0;
        };
    }
}
