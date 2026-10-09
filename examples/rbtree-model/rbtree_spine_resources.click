// The anchor keeps only its left link in the spine; transplanting its other
// fields does not require opening or rebuilding the descent path.
import "rbtree_resources.click";
import "rbtree_spine_model.click";

resource erase_spine_at(focus: struct rb_node*, anchor: struct rb_node*) {
    field model: EraseSpine;
    match model {
        EraseSpine::Top => {
            owns anchor->rb_left;
            fact anchor != 0;
            fact anchor->rb_left == focus;
        },
        EraseSpine::Left(identity, grandparent, color, sibling_model, up_model) => {
            owns identity->__rb_parent_color;
            owns identity->rb_left;
            owns identity->rb_right;
            owns sibling: rb_at(identity->rb_right);
            owns up: erase_spine_at(identity, anchor);
            fact identity != 0;
            fact aligned(identity, 8);
            fact aligned(grandparent, 8);
            fact identity->rb_left == focus;
            fact identity->__rb_parent_color
                == address(grandparent) + (identity->__rb_parent_color & 1);
            fact (identity->__rb_parent_color & 1) == color_bit(color);
            fact sibling.model == sibling_model;
            fact up.model == up_model;
            fact rb_parent_is(sibling_model, identity) == 1;
        },
    }
}

resource erase_left_at(anchor: struct rb_node*) {
    field model: RbTree;
    owns anchor->rb_left;
    owns tree: rb_at(anchor->rb_left);
    fact anchor != 0;
    fact tree.model == model;
}

resource erase_spine_frame(parent: struct rb_node*, anchor: struct rb_node*) {
    field model: EraseSpine;
    match model {
        EraseSpine::Top => {
            fact parent == anchor;
            fact anchor != 0;
        },
        EraseSpine::Left(identity, grandparent, color, sibling_model, up_model) => {
            owns identity->__rb_parent_color;
            owns identity->rb_right;
            owns sibling: rb_at(identity->rb_right);
            owns up: erase_spine_at(identity, anchor);
            fact parent == identity;
            fact identity != 0;
            fact aligned(identity, 8);
            fact aligned(grandparent, 8);
            fact identity->__rb_parent_color
            == address(grandparent) + (identity->__rb_parent_color & 1);
            fact (identity->__rb_parent_color & 1) == color_bit(color);
            fact sibling.model == sibling_model;
            fact up.model == up_model;
            fact rb_parent_is(sibling_model, identity) == 1;
        },
    }
}

resource erase_anchor_frame(anchor: struct rb_node*, root: struct rb_root*) {
    field model: EraseAnchorFrame;
    match model {
        EraseAnchorFrame::At(parent, color, sibling_model, above) => {
            owns anchor->__rb_parent_color;
            owns anchor->rb_right;
            owns right: rb_at(anchor->rb_right);
            owns up: ctx_at(anchor, root);
            fact anchor != 0;
            fact aligned(anchor, 8);
            fact aligned(parent, 8);
            fact anchor->__rb_parent_color == address(parent) + (anchor->__rb_parent_color & 1);
            fact (anchor->__rb_parent_color & 1) == color_bit(color);
            fact right.model == sibling_model;
            fact up.model == above;
            fact rb_parent_is(sibling_model, anchor) == 1;
            fact ctx_node_is(above, parent) == 1;
            fact above == ctx_reroot(above, parent);
        },
    }
}
