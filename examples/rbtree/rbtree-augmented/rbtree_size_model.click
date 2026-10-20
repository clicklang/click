arithmetic "integer";

verifying "rbtree_size_compute.c";
verifying "rbtree_size_copy.c";
import "rbtree_size_compute.click";
import "rbtree_subtree_size.click";
import "../rbtree-model/rbtree_resources.click";

spec enum SizedTree {
    Empty,
    Node(struct rb_node*, struct rb_node*, Color, int32, SizedTree, SizedTree),
}

function sized_shape(tree: SizedTree) -> RbTree
    decreases tree
{
    match tree {
        SizedTree::Empty => RbTree::Empty,
        SizedTree::Node(node, parent, color, value, left, right) =>
            RbTree::Node(node, parent, color, sized_shape(left), sized_shape(right)),
    }
}

function sized_value(tree: SizedTree) -> int32 {
    match tree {
        SizedTree::Empty => 0,
        SizedTree::Node(node, parent, color, value, left, right) => value,
    }
}

function sized_left(tree: SizedTree) -> SizedTree {
    match tree {
        SizedTree::Empty => SizedTree::Empty,
        SizedTree::Node(node, parent, color, value, left, right) => left,
    }
}

function sized_right(tree: SizedTree) -> SizedTree {
    match tree {
        SizedTree::Empty => SizedTree::Empty,
        SizedTree::Node(node, parent, color, value, left, right) => right,
    }
}

function sized_parent_is(tree: SizedTree, parent: struct rb_node*) -> int32 {
    match tree {
        SizedTree::Empty => 1,
        SizedTree::Node(node, actual, color, value, left, right) =>
            if actual == parent { 1 } else { 0 },
    }
}

// This predicate concerns counts only; links and ownership remain in sized_at.
function sized_counts_valid(tree: SizedTree) -> int32
    decreases tree
{
    match tree {
        SizedTree::Empty => 1,
        SizedTree::Node(node, parent, color, value, left, right) =>
            if to_integer(value) == 1 + to_integer(sized_value(left)) + to_integer(sized_value(right))
            {
                if sized_counts_valid(left) == 1 {
                    if sized_counts_valid(right) == 1 { 1 } else { 0 }
                } else { 0 }
            } else { 0 },
    }
}

resource sized_at(p: struct rb_node*) {
    field model: SizedTree;
    match model {
        SizedTree::Empty => { fact p == 0; },
        SizedTree::Node(identity, parent, color, value, left_model, right_model) => {
            owns p->__rb_parent_color;
            owns p->rb_left;
            owns p->rb_right;
            owns metadata: size_metadata(p);
            owns left: sized_at(p->rb_left);
            owns right: sized_at(p->rb_right);
            fact metadata.value == value;
            fact left.model == left_model;
            fact right.model == right_model;
            fact p != 0;
            fact p == identity;
            fact p->rb_left != p;
            fact p->rb_right != p;
            fact aligned(p, 8);
            fact aligned(parent, 8);
            fact p->__rb_parent_color == address(parent) + (p->__rb_parent_color & 1);
            fact ((struct rb_node*)(p->__rb_parent_color & ~3)) == parent;
            fact (p->__rb_parent_color & 1) == color_bit(color);
            fact sized_parent_is(left_model, p) == 1;
            fact sized_parent_is(right_model, p) == 1;
            fact to_integer(value) == 1 + to_integer(sized_value(left_model)) + to_integer(sized_value(right_model));
        },
    }
}

theorem sized_child_descent(identity: struct rb_node*, parent: struct rb_node*, color: Color,
                           value: int32, left: SizedTree, right: SizedTree) {
    ensures 0 <= rb_subtree_size(sized_shape(left)) by {
        apply(rb_subtree_size_nonnegative(sized_shape(left)));
        assumption();
    }
    ensures 0 <= rb_subtree_size(sized_shape(right)) by {
        apply(rb_subtree_size_nonnegative(sized_shape(right)));
        assumption();
    }
    ensures rb_subtree_size(sized_shape(left)) < rb_subtree_size(sized_shape(SizedTree::Node(identity, parent, color, value, left, right))) by {
        apply(rb_subtree_size_nonnegative(sized_shape(right)));
        unfold(sized_shape(SizedTree::Node(identity, parent, color, value, left, right)));
        unfold(rb_subtree_size(RbTree::Node(identity, parent, color, sized_shape(left), sized_shape(right))));
        arithmetic() using { rb_subtree_size(sized_shape(right)) >= 0; };
    }
    ensures rb_subtree_size(sized_shape(right)) < rb_subtree_size(sized_shape(SizedTree::Node(identity, parent, color, value, left, right))) by {
        apply(rb_subtree_size_nonnegative(sized_shape(left)));
        unfold(sized_shape(SizedTree::Node(identity, parent, color, value, left, right)));
        unfold(rb_subtree_size(RbTree::Node(identity, parent, color, sized_shape(left), sized_shape(right))));
        arithmetic() using { rb_subtree_size(sized_shape(left)) >= 0; };
    }
}

tactic certify_size(p: struct rb_node*) {
    consumes tree: sized_at(p);
    decreases rb_subtree_size(sized_shape(tree.model));
    produces checked: sized_at(p);
    ensures checked.model == old(tree.model);
    ensures to_integer(sized_value(checked.model)) == rb_subtree_size(sized_shape(checked.model));
    ensures sized_counts_valid(checked.model) == 1;
} by {
    match tree.model {
        SizedTree::Empty => {
            unfold(tree);
            let checked = fold(sized_at(p), { model: SizedTree::Empty });
            have checked.model == old(tree.model);
            have sized_counts_valid(checked.model) == 1 by {
                rewrite(checked.model == SizedTree::Empty);
                unfold(sized_counts_valid(SizedTree::Empty));
                normalize();
            }
            have to_integer(sized_value(checked.model)) == rb_subtree_size(sized_shape(checked.model)) by {
                rewrite(checked.model == SizedTree::Empty);
                unfold(sized_value(SizedTree::Empty));
                unfold(sized_shape(SizedTree::Empty));
                unfold(rb_subtree_size(RbTree::Empty));
                normalize();
            }
        },
        SizedTree::Node(identity, parent, color, value, left_model, right_model) => {
            let { metadata: metadata, left: left, right: right } = unfold(tree);
            apply(sized_child_descent(identity, parent, color, value, left_model, right_model));
            have rb_subtree_size(sized_shape(old(tree.model))) == rb_subtree_size(sized_shape(left_model)) + rb_subtree_size(sized_shape(right_model)) + 1 by {
                rewrite(old(tree.model) == SizedTree::Node(identity, parent, color, value, left_model, right_model));
                unfold(sized_shape(SizedTree::Node(identity, parent, color, value, left_model, right_model)));
                unfold(rb_subtree_size(RbTree::Node(identity, parent, color, sized_shape(left_model), sized_shape(right_model))));
                normalize();
            }
            have 0 <= rb_subtree_size(sized_shape(left.model)) by {
                rewrite(left.model == left_model);
                assumption();
            }
            have rb_subtree_size(sized_shape(left.model)) < rb_subtree_size(sized_shape(old(tree.model))) by {
                rewrite(left.model == left_model);
                rewrite(old(tree.model) == SizedTree::Node(identity, parent, color, value, left_model, right_model));
                assumption();
            }
            let { checked: left } = certify_size(p->rb_left, { tree: left });
            have 0 <= rb_subtree_size(sized_shape(right.model)) by {
                rewrite(right.model == right_model);
                assumption();
            }
            have rb_subtree_size(sized_shape(right.model)) < rb_subtree_size(sized_shape(old(tree.model))) by {
                rewrite(right.model == right_model);
                rewrite(old(tree.model) == SizedTree::Node(identity, parent, color, value, left_model, right_model));
                assumption();
            }
            let { checked: right } = certify_size(p->rb_right, { tree: right });
            have to_integer(sized_value(left_model)) == rb_subtree_size(sized_shape(left_model)) by {
                rewrite(left_model == left.model);
                assumption();
            }
            have to_integer(sized_value(right_model)) == rb_subtree_size(sized_shape(right_model)) by {
                rewrite(right_model == right.model);
                assumption();
            }
            have to_integer(value) == rb_subtree_size(sized_shape(old(tree.model))) by {
                arithmetic() using {
                    to_integer(value) == 1 + to_integer(sized_value(left_model)) + to_integer(sized_value(right_model));
                    to_integer(sized_value(left_model)) == rb_subtree_size(sized_shape(left_model));
                    to_integer(sized_value(right_model)) == rb_subtree_size(sized_shape(right_model));
                    rb_subtree_size(sized_shape(old(tree.model))) == rb_subtree_size(sized_shape(left_model)) + rb_subtree_size(sized_shape(right_model)) + 1;
                };
            }
            have sized_counts_valid(left_model) == 1 by { rewrite(left_model == left.model); assumption(); }
            have sized_counts_valid(right_model) == 1 by { rewrite(right_model == right.model); assumption(); }
            let checked = fold(sized_at(p), { model: SizedTree::Node(identity, parent, color, value, left_model, right_model) }, { metadata: metadata, left: left, right: right });
            have checked.model == old(tree.model);
            have sized_counts_valid(checked.model) == 1 by {
                rewrite(checked.model == SizedTree::Node(identity, parent, color, value, left_model, right_model));
                unfold(sized_counts_valid(SizedTree::Node(identity, parent, color, value, left_model, right_model)));
                normalize() using {
                    to_integer(value) == 1 + to_integer(sized_value(left_model)) + to_integer(sized_value(right_model));
                    sized_counts_valid(left_model) == 1;
                    sized_counts_valid(right_model) == 1;
                };
            }
            have to_integer(sized_value(checked.model)) == rb_subtree_size(sized_shape(checked.model)) by {
                rewrite(checked.model == SizedTree::Node(identity, parent, color, value, left_model, right_model));
                unfold(sized_value(SizedTree::Node(identity, parent, color, value, left_model, right_model)));
                rewrite(SizedTree::Node(identity, parent, color, value, left_model, right_model) == old(tree.model));
                assumption();
            }
        },
    }
}

// Erasing metadata preserves the parent predicate used by ownership resources.
theorem sized_parent_is_shape(tree: SizedTree, parent: struct rb_node*) {
    ensures sized_parent_is(tree, parent) == rb_parent_is(sized_shape(tree), parent) by {
        induct(tree) as ih {
            SizedTree::Empty => {
                unfold(sized_parent_is(SizedTree::Empty, parent));
                unfold(sized_shape(SizedTree::Empty));
                unfold(rb_parent_is(RbTree::Empty, parent));
                normalize();
            },
            SizedTree::Node(identity, before, color, value, left, right) => {
                unfold(sized_parent_is(SizedTree::Node(identity, before, color, value, left, right), parent));
                unfold(sized_shape(SizedTree::Node(identity, before, color, value, left, right)));
                unfold(rb_parent_is(RbTree::Node(identity, before, color, sized_shape(left), sized_shape(right)), parent));
                normalize();
            },
        }
    }
}
