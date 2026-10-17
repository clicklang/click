import "rbtree_model.click";

resource rb_at(p: struct rb_node*) {
    field model: RbTree;
    match model {
        RbTree::Empty => { fact p == 0; },
        RbTree::Node(identity, parent, color, left_model, right_model) => {
            owns p->__rb_parent_color;
            owns p->rb_left;
            owns p->rb_right;
            owns left: rb_at(p->rb_left);
            owns right: rb_at(p->rb_right);
            fact p != 0;
            fact p == identity;
            fact aligned(p, 8);
            fact aligned(parent, 8);
            fact p->__rb_parent_color == address(parent) + (p->__rb_parent_color & 1);
            fact ((struct rb_node*)(p->__rb_parent_color & ~3)) == parent;
            fact (p->__rb_parent_color & 1) == color_bit(color);
            fact left.model == left_model;
            fact right.model == right_model;
            fact rb_parent_is(left_model, p) == 1;
            fact rb_parent_is(right_model, p) == 1;
        },
    }
}

resource ctx_at(child: struct rb_node*, root: struct rb_root*) {
    field model: Context;
    match model {
        Context::Top => {
            owns root->rb_node;
            fact root != 0;
            fact root->rb_node == child;
        },
        Context::Left(identity, grandparent, color, sibling_model, up_model) => {
            owns identity->__rb_parent_color;
            owns identity->rb_left;
            owns identity->rb_right;
            owns sibling: rb_at(identity->rb_right);
            owns up: ctx_at(identity, root);
            fact identity != 0;
            fact aligned(identity, 8);
            fact aligned(grandparent, 8);
            fact identity->rb_left == child;
            fact identity->__rb_parent_color
                == address(grandparent) + (identity->__rb_parent_color & 1);
            fact ((struct rb_node*)(identity->__rb_parent_color & ~3)) == grandparent;
            fact (identity->__rb_parent_color & 1) == color_bit(color);
            fact sibling.model == sibling_model;
            fact up.model == up_model;
            fact rb_parent_is(sibling_model, identity) == 1;
            fact ctx_node_is(up_model, grandparent) == 1;
            fact up_model == ctx_reroot(up_model, grandparent);
        },
        Context::Right(identity, grandparent, color, sibling_model, up_model) => {
            owns identity->__rb_parent_color;
            owns identity->rb_left;
            owns identity->rb_right;
            owns sibling: rb_at(identity->rb_left);
            owns up: ctx_at(identity, root);
            fact identity != 0;
            fact aligned(identity, 8);
            fact aligned(grandparent, 8);
            fact identity->rb_right == child;
            fact identity->__rb_parent_color
                == address(grandparent) + (identity->__rb_parent_color & 1);
            fact ((struct rb_node*)(identity->__rb_parent_color & ~3)) == grandparent;
            fact (identity->__rb_parent_color & 1) == color_bit(color);
            fact sibling.model == sibling_model;
            fact up.model == up_model;
            fact rb_parent_is(sibling_model, identity) == 1;
            fact ctx_node_is(up_model, grandparent) == 1;
            fact up_model == ctx_reroot(up_model, grandparent);
        },
    }
}

resource rb_root_at(root: struct rb_root*) {
    field model: RbTree;
    owns root->rb_node;
    owns tree: rb_at(root->rb_node);
    fact root != 0;
    fact tree.model == model;
}
