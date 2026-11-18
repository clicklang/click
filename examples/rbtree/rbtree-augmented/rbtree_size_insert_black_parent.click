// The non-root, black-parent exit makes no writes and invokes no callback.
verifying "rb_insert_augmented.c";
verifying "rbtree_size_copy.c";
verifying "rbtree_size_compute.c";
import "rbtree_size_metadata.click";

resource sized_black_parent_at(node: struct rb_node*) {
    field model: SizedTree;
    field parent_tag: uint64;
    match model {
        SizedTree::Empty => { fact 0 == 1; },
        SizedTree::Node(identity, ancestor, shade, value, left_model, right_model) => {
            owns ancestor->__rb_parent_color;
            owns tree: sized_at(node);
            fact ancestor->__rb_parent_color == parent_tag;
            fact ancestor != 0;
            fact (ancestor->__rb_parent_color & 1) == 1;
            fact shade == Color::Red;
            fact tree.model == model;
        },
    }
}

// Keep the ancestor's packed word through the read-only C steps.
resource black_parent_observation(ancestor: struct rb_node*) {
    field tag: uint64;
    owns ancestor->__rb_parent_color;
    fact ancestor->__rb_parent_color == tag;
    fact (ancestor->__rb_parent_color & 1) == 1;
}

void __rb_insert(struct rb_node* node, struct rb_root* root,
                  void (*augment_rotate)(struct rb_node*, struct rb_node*)) {
    owns state: sized_black_parent_at(node);
    ensures state.model == old(state.model);
    ensures state.parent_tag == old(state.parent_tag);
} by {
    match state.model {
        SizedTree::Empty => {
            unfold(state);
            contradiction(0 == 1);
        },
        SizedTree::Node(identity, ancestor, shade, value, left_model, right_model) => {
            let { tree: tree, parent_tag: parent_tag } = unfold(state);
            let { metadata: metadata, left: left, right: right } = unfold(tree);
            have shade == Color::Red by solve();
            have (node->__rb_parent_color & 1) == color_bit(Color::Red) by {
                rewrite(Color::Red, shade); known();
            }
            unfold(color_bit(Color::Red));
            have (node->__rb_parent_color & 1) == 0 by {
                rewrite((node->__rb_parent_color & 1), color_bit(Color::Red));
                rewrite(color_bit(Color::Red), 0); normalize();
            }
            have node->__rb_parent_color == address(ancestor) by {
                rewrite(node->__rb_parent_color, address(ancestor) + (node->__rb_parent_color & 1));
                rewrite((node->__rb_parent_color & 1), 0); normalize();
            }
            have ancestor->__rb_parent_color == parent_tag by known();
            let observation = fold(black_parent_observation(ancestor), { tag: parent_tag });
            step(); step(); step(); step();
            unfold(observation);
            have ancestor->__rb_parent_color == parent_tag by known();
            have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == ancestor by solve();
            let tree = fold(sized_at(node), { model: old(state.model) }, { metadata: metadata, left: left, right: right });
            let state = fold(sized_black_parent_at(node), { model: old(state.model), parent_tag: parent_tag }, { tree: tree });
            step(); // Declare tmp before the C loop.
            loop {
                owns state: sized_black_parent_at(node);
                decreases 0;
                invariant node == old(node);
                invariant parent == ancestor;
                invariant state.model == SizedTree::Node(identity, ancestor, Color::Red, value, left_model, right_model);
                invariant state.model == old(state.model);
                invariant state.parent_tag == old(state.parent_tag);
                initialize by solve();
                preserve by {
                    let { tree: tree, parent_tag: loop_tag } = unfold(state);
                    have ancestor->__rb_parent_color == loop_tag by known();
                    let observation = fold(black_parent_observation(ancestor), { tag: loop_tag });
                    step(); step();
                    unfold(observation);
                    have ancestor->__rb_parent_color == loop_tag by known();
                    let state = fold(sized_black_parent_at(node), { model: old(state.model), parent_tag: loop_tag }, { tree: tree });
                    step(); step();
                }
            }
            have node == old(node) by { known(); }
            step_until(function.exit);
        },
    }
}

void __rb_insert_augmented(struct rb_node* node, struct rb_root* root,
                  void (*augment_rotate)(struct rb_node*, struct rb_node*)) {
    owns state: sized_black_parent_at(node);
    ensures state.model == old(state.model);
    ensures state.parent_tag == old(state.parent_tag);
} by {
    step(__rb_insert, { state: state });
}

void rb_insert_augmented(struct rb_node* node, struct rb_root* root,
                  const struct rb_augment_callbacks* augment) {
    views augment->rotate;
    owns state: sized_black_parent_at(node);
    ensures state.model == old(state.model);
    ensures state.parent_tag == old(state.parent_tag);
} by {
    step(__rb_insert_augmented, { state: state });
}
