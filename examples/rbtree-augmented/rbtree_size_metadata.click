verifying "rbtree_size_compute.c";
verifying "rbtree_size_copy.c";
import "rbtree_size_model.click";

function sized_identity(tree: SizedTree) -> struct rb_node* {
    match tree {
        SizedTree::Empty => 0,
        SizedTree::Node(identity, parent, color, value, left, right) => identity,
    }
}

// This owns cache cells only. Its logical shape may outlive a link update.
resource sized_metadata_at(p: struct rb_node*) {
    field model: SizedTree;
    match model {
        SizedTree::Empty => { fact p == 0; },
        SizedTree::Node(identity, parent, color, value, left_model, right_model) => {
            owns value_cell: size_metadata(p);
            owns left: sized_metadata_at(sized_identity(left_model));
            owns right: sized_metadata_at(sized_identity(right_model));
            fact left.model == left_model;
            fact right.model == right_model;
            fact p == identity;
            fact p != 0;
            fact value_cell.value == value;
            fact sized_identity(left_model) != p;
            fact sized_identity(right_model) != p;
        },
    }
}

tactic split_sized_tree(p: struct rb_node*) {
    consumes tree: sized_at(p);
    decreases rb_subtree_size(sized_shape(tree.model));
    produces structure: rb_at(p);
    produces metadata: sized_metadata_at(p);
    ensures structure.model == sized_shape(old(tree.model));
    ensures metadata.model == old(tree.model);
    ensures sized_identity(metadata.model) == p;
} by {
    match tree.model {
        SizedTree::Empty => {
            unfold(tree);
            let structure = fold(rb_at(p), { model: RbTree::Empty });
            let metadata = fold(sized_metadata_at(p), { model: SizedTree::Empty });
            have sized_shape(SizedTree::Empty) == RbTree::Empty by { unfold(sized_shape(SizedTree::Empty)); normalize(); }
            have sized_identity(metadata.model) == p by { rewrite(metadata.model == SizedTree::Empty); unfold(sized_identity(SizedTree::Empty)); normalize(); }
        },
        SizedTree::Node(identity, parent, color, value, left_model, right_model) => {
            apply(sized_child_descent(identity, parent, color, value, left_model, right_model));
            let { metadata: cell, left: left, right: right } = unfold(tree);
            have rb_subtree_size(sized_shape(left.model)) < rb_subtree_size(sized_shape(old(tree.model))) by {
                rewrite(left.model == left_model);
                rewrite(old(tree.model) == SizedTree::Node(identity, parent, color, value, left_model, right_model)); assumption();
            }
            have rb_subtree_size(sized_shape(right.model)) < rb_subtree_size(sized_shape(old(tree.model))) by {
                rewrite(right.model == right_model);
                rewrite(old(tree.model) == SizedTree::Node(identity, parent, color, value, left_model, right_model)); assumption();
            }
            let { structure: left_structure, metadata: left_metadata } = split_sized_tree(p->rb_left, { tree: left });
            let { structure: right_structure, metadata: right_metadata } = split_sized_tree(p->rb_right, { tree: right });
            apply(sized_parent_is_shape(left_model, p));
            apply(sized_parent_is_shape(right_model, p));
            have rb_parent_is(sized_shape(left_model), p) == 1 by {
                rewrite(rb_parent_is(sized_shape(left_model), p) == sized_parent_is(left_model, p)); assumption();
            }
            have rb_parent_is(sized_shape(right_model), p) == 1 by {
                rewrite(rb_parent_is(sized_shape(right_model), p) == sized_parent_is(right_model, p)); assumption();
            }
            have sized_identity(left_model) == p->rb_left by {
                rewrite(left_model == left_metadata.model); assumption();
            }
            have sized_identity(right_model) == p->rb_right by {
                rewrite(right_model == right_metadata.model); assumption();
            }
            have sized_identity(left_model) != p by {
                rewrite(sized_identity(left_model) == p->rb_left); assumption();
            }
            have sized_identity(right_model) != p by {
                rewrite(sized_identity(right_model) == p->rb_right); assumption();
            }
            let structure = fold(rb_at(p), { model: RbTree::Node(identity, parent, color, sized_shape(left_model), sized_shape(right_model)) }, { left: left_structure, right: right_structure });
            let metadata = fold(sized_metadata_at(p), { model: SizedTree::Node(identity, parent, color, value, left_model, right_model) }, { value_cell: cell, left: left_metadata, right: right_metadata });
            have structure.model == sized_shape(old(tree.model)) by {
                rewrite(old(tree.model) == SizedTree::Node(identity, parent, color, value, left_model, right_model));
                unfold(sized_shape(SizedTree::Node(identity, parent, color, value, left_model, right_model))); normalize();
            }
            have sized_identity(metadata.model) == p by {
                rewrite(metadata.model == SizedTree::Node(identity, parent, color, value, left_model, right_model));
                unfold(sized_identity(SizedTree::Node(identity, parent, color, value, left_model, right_model))); assumption();
            }
        },
    }
}

function rb_identity(tree: RbTree) -> struct rb_node* {
    match tree {
        RbTree::Empty => 0,
        RbTree::Node(identity, parent, color, left, right) => identity,
    }
}

theorem sized_identity_shape(tree: SizedTree) {
    ensures sized_identity(tree) == rb_identity(sized_shape(tree)) by {
        induct(tree) as ih {
            SizedTree::Empty => {
                unfold(sized_shape(SizedTree::Empty));
                unfold(sized_identity(SizedTree::Empty));
                unfold(rb_identity(RbTree::Empty)); normalize();
            },
            SizedTree::Node(identity, parent, color, value, left, right) => {
                unfold(sized_shape(SizedTree::Node(identity, parent, color, value, left, right)));
                unfold(sized_identity(SizedTree::Node(identity, parent, color, value, left, right)));
                unfold(rb_identity(RbTree::Node(identity, parent, color, sized_shape(left), sized_shape(right)))); normalize();
            },
        }
    }
}

tactic rb_identity_at(p: struct rb_node*) {
    consumes tree: rb_at(p);
    produces checked: rb_at(p);
    ensures checked.model == old(tree.model);
    ensures rb_identity(checked.model) == p;
} by {
    match tree.model {
        RbTree::Empty => {
            unfold(tree);
            let checked = fold(rb_at(p), { model: RbTree::Empty });
            have rb_identity(checked.model) == p by {
                rewrite(checked.model == RbTree::Empty); unfold(rb_identity(RbTree::Empty)); normalize();
            }
        },
        RbTree::Node(identity, parent, color, left_model, right_model) => {
            let { left: left, right: right } = unfold(tree);
            let checked = fold(rb_at(p), { model: RbTree::Node(identity, parent, color, left_model, right_model) }, { left: left, right: right });
            have rb_identity(checked.model) == p by {
                rewrite(checked.model == RbTree::Node(identity, parent, color, left_model, right_model));
                unfold(rb_identity(RbTree::Node(identity, parent, color, left_model, right_model))); assumption();
            }
        },
    }
}

theorem sized_valid_parts(identity: struct rb_node*, parent: struct rb_node*, color: Color,
                          value: int32, left: SizedTree, right: SizedTree) {
    requires sized_counts_valid(SizedTree::Node(identity, parent, color, value, left, right)) == 1;
    ensures to_integer(value) == 1 + to_integer(sized_value(left)) + to_integer(sized_value(right)) by auto;
    ensures sized_counts_valid(left) == 1 by auto;
    ensures sized_counts_valid(right) == 1 by auto;
}

tactic join_sized_tree(p: struct rb_node*) {
    consumes structure: rb_at(p);
    consumes metadata: sized_metadata_at(p);
    requires structure.model == sized_shape(metadata.model);
    requires sized_counts_valid(metadata.model) == 1;
    decreases rb_subtree_size(sized_shape(metadata.model));
    produces tree: sized_at(p);
    ensures tree.model == old(metadata.model);
} by {
    match metadata.model {
        SizedTree::Empty => {
            have structure.model == RbTree::Empty by {
                rewrite(structure.model == sized_shape(metadata.model));
                rewrite(metadata.model == SizedTree::Empty);
                unfold(sized_shape(SizedTree::Empty)); normalize();
            }
            unfold(structure); unfold(metadata);
            let tree = fold(sized_at(p), { model: SizedTree::Empty });
        },
        SizedTree::Node(identity, parent, color, value, left_model, right_model) => {
            have structure.model == RbTree::Node(identity, parent, color, sized_shape(left_model), sized_shape(right_model)) by {
                rewrite(structure.model == sized_shape(metadata.model));
                rewrite(metadata.model == SizedTree::Node(identity, parent, color, value, left_model, right_model));
                unfold(sized_shape(SizedTree::Node(identity, parent, color, value, left_model, right_model))); normalize();
            }
            have sized_counts_valid(SizedTree::Node(identity, parent, color, value, left_model, right_model)) == 1 by {
                rewrite(SizedTree::Node(identity, parent, color, value, left_model, right_model) == metadata.model); assumption();
            }
            apply(sized_valid_parts(identity, parent, color, value, left_model, right_model));
            let { value_cell: cell, left: left_metadata, right: right_metadata } = unfold(metadata);
            let { left: left_structure, right: right_structure } = unfold(structure);
            let { checked: left_structure } = rb_identity_at(p->rb_left, { tree: left_structure });
            let { checked: right_structure } = rb_identity_at(p->rb_right, { tree: right_structure });
            apply(sized_identity_shape(left_model)); apply(sized_identity_shape(right_model));
            have rb_identity(sized_shape(left_model)) == p->rb_left by {
                rewrite(sized_shape(left_model) == left_structure.model); assumption();
            }
            have rb_identity(sized_shape(right_model)) == p->rb_right by {
                rewrite(sized_shape(right_model) == right_structure.model); assumption();
            }
            have sized_identity(left_model) == p->rb_left by {
                rewrite(sized_identity(left_model) == rb_identity(sized_shape(left_model))); assumption();
            }
            have sized_identity(right_model) == p->rb_right by {
                rewrite(sized_identity(right_model) == rb_identity(sized_shape(right_model))); assumption();
            }
            have p->rb_left != p by assumption();
            have p->rb_right != p by assumption();
            apply(sized_child_descent(identity, parent, color, value, left_model, right_model));
            have rb_subtree_size(sized_shape(left_metadata.model)) < rb_subtree_size(sized_shape(old(metadata.model))) by {
                rewrite(left_metadata.model == left_model);
                rewrite(old(metadata.model) == SizedTree::Node(identity, parent, color, value, left_model, right_model)); assumption();
            }
            have rb_subtree_size(sized_shape(right_metadata.model)) < rb_subtree_size(sized_shape(old(metadata.model))) by {
                rewrite(right_metadata.model == right_model);
                rewrite(old(metadata.model) == SizedTree::Node(identity, parent, color, value, left_model, right_model)); assumption();
            }
            let { tree: left } = join_sized_tree(p->rb_left, { structure: left_structure, metadata: left_metadata });
            let { tree: right } = join_sized_tree(p->rb_right, { structure: right_structure, metadata: right_metadata });
            apply(sized_parent_is_shape(left_model, p)); apply(sized_parent_is_shape(right_model, p));
            have sized_parent_is(left_model, p) == 1 by {
                rewrite(sized_parent_is(left_model, p) == rb_parent_is(sized_shape(left_model), p)); assumption();
            }
            have sized_parent_is(right_model, p) == 1 by {
                rewrite(sized_parent_is(right_model, p) == rb_parent_is(sized_shape(right_model), p)); assumption();
            }
            let tree = fold(sized_at(p), { model: SizedTree::Node(identity, parent, color, value, left_model, right_model) }, { metadata: cell, left: left, right: right });
        },
    }
}
