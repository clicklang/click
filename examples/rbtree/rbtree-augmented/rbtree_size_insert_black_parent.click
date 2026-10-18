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
            let { tree: tree } = unfold(state);
            let { metadata: metadata, left: left, right: right } = unfold(tree);
            have shade == Color::Red by simp();
            have (node->__rb_parent_color & 1) == color_bit(Color::Red) by {
                rewrite(Color::Red == shade); assumption();
            }
            unfold(color_bit(Color::Red));
            have (node->__rb_parent_color & 1) == 0 by {
                rewrite((node->__rb_parent_color & 1) == color_bit(Color::Red));
                rewrite(color_bit(Color::Red) == 0); normalize();
            }
            have node->__rb_parent_color == address(ancestor) by {
                rewrite(node->__rb_parent_color == address(ancestor) + (node->__rb_parent_color & 1));
                rewrite((node->__rb_parent_color & 1) == 0); normalize();
            }
            step(); step(); step(); step();
            let tree = fold(sized_at(node), { model: old(state.model) }, { metadata: metadata, left: left, right: right });
            let state = fold(sized_black_parent_at(node), { model: old(state.model), parent_tag: old(state.parent_tag) }, { tree: tree });
            loop {
                owns state: sized_black_parent_at(node);
                decreases 0;
                invariant node == old(node);
                invariant parent == ancestor;
                invariant state.model == SizedTree::Node(identity, ancestor, Color::Red, value, left_model, right_model);
                invariant state.model == old(state.model);
                invariant state.parent_tag == old(state.parent_tag);
                initialize by simp();
                preserve by {
                    let { tree: tree } = unfold(state);
                    step(); step();
                    let state = fold(sized_black_parent_at(node), { model: old(state.model), parent_tag: old(state.parent_tag) }, { tree: tree });
                    step(); step();
                }
            }
            have node == old(node) by { assumption(); }
            execute(); simp();
        },
    }
}

void __rb_insert_augmented(struct rb_node* node, struct rb_root* root,
                  void (*augment_rotate)(struct rb_node*, struct rb_node*)) {
    owns state: sized_black_parent_at(node);
    ensures state.model == old(state.model);
    ensures state.parent_tag == old(state.parent_tag);
} by {
    step(__rb_insert(node, root, augment_rotate), { state: state });
    execute(); simp();
}

void rb_insert_augmented(struct rb_node* node, struct rb_root* root,
                  const struct rb_augment_callbacks* augment) {
    views augment->rotate;
    owns state: sized_black_parent_at(node);
    ensures state.model == old(state.model);
    ensures state.parent_tag == old(state.parent_tag);
} by {
    step(__rb_insert_augmented(node, root, augment->rotate), { state: state });
    execute(); simp();
}
