// Root-only insertion boundary: no rotation callback is invoked.
// The child subtrees may be nonempty; their cached sizes remain owned and valid.
verifying "rb_insert_augmented.c";
verifying "rbtree_size_copy.c";
verifying "rbtree_size_compute.c";
import "rbtree_size_metadata.click";

function sized_recolor(tree: SizedTree, color: Color) -> SizedTree {
    match tree {
        SizedTree::Empty => SizedTree::Empty,
        SizedTree::Node(node, parent, before, value, left, right) =>
            SizedTree::Node(node, parent, color, value, left, right),
    }
}

contract void InsertSizedRoot(struct rb_node* node, struct rb_root* root,
                  void (*augment_rotate)(struct rb_node*, struct rb_node*)) {
    owns root->rb_node;
    owns tree: sized_at(node);
    requires root->rb_node == node;
    requires tree.model == SizedTree::Node(node, 0, Color::Red, sized_value(tree.model), sized_left(tree.model), sized_right(tree.model));
    ensures root->rb_node == node;
    ensures tree.model == sized_recolor(old(tree.model), Color::Black);
}

void __rb_insert(struct rb_node* node, struct rb_root* root,
                  void (*augment_rotate)(struct rb_node*, struct rb_node*)) {
    owns root->rb_node;
    owns tree: sized_at(node);
    requires root->rb_node == node;
    requires tree.model == SizedTree::Node(node, 0, Color::Red, sized_value(tree.model), sized_left(tree.model), sized_right(tree.model));
    ensures root->rb_node == node;
    ensures tree.model == sized_recolor(old(tree.model), Color::Black);
} by {
    let { metadata: metadata, left: left, right: right } = unfold(tree);
    unfold(color_bit(Color::Red));
    have (node->__rb_parent_color & 1) == 0 by {
        rewrite((node->__rb_parent_color & 1) == color_bit(Color::Red));
        rewrite(color_bit(Color::Red) == 0);
        normalize();
    }
    have node->__rb_parent_color == 0 by {
        rewrite(node->__rb_parent_color == address(0) + (node->__rb_parent_color & 1));
        rewrite((node->__rb_parent_color & 1) == 0);
        normalize();
    }
    step(); step(); step(); step();
    let tree = fold(sized_at(node), { model: old(tree.model) }, { metadata: metadata, left: left, right: right });
    loop {
        owns root->rb_node;
        owns tree: sized_at(node);
        decreases 0;
        invariant parent == 0;
        invariant node == old(node);
        invariant root->rb_node == node;
        invariant tree.model == old(tree.model);
        invariant old(tree.model) == SizedTree::Node(node, 0, Color::Red, sized_value(old(tree.model)), sized_left(old(tree.model)), sized_right(old(tree.model)));
        invariant tree.model == SizedTree::Node(node, 0, Color::Red, sized_value(tree.model), sized_left(tree.model), sized_right(tree.model));
        initialize by simp;
        preserve by {
            let { metadata: metadata, left: left, right: right } = unfold(tree);
            step(); step();
            have (node->__rb_parent_color & 1) == color_bit(Color::Black) by {
                unfold(color_bit(Color::Black)); simp();
            }
            let tree = fold(sized_at(node), {
                model: SizedTree::Node(node, 0, Color::Black, sized_value(old(tree.model)), sized_left(old(tree.model)), sized_right(old(tree.model)))
            }, { metadata: metadata, left: left, right: right });
            have tree.model == sized_recolor(old(tree.model), Color::Black) by {
                rewrite(old(tree.model) == SizedTree::Node(node, 0, Color::Red, sized_value(old(tree.model)), sized_left(old(tree.model)), sized_right(old(tree.model))));
                unfold(sized_recolor(SizedTree::Node(node, 0, Color::Red, sized_value(old(tree.model)), sized_left(old(tree.model)), sized_right(old(tree.model))), Color::Black));
                simp();
            }
            step();
        }
    }
    have node == old(node) by { assumption(); }
    execute(); simp();
}

theorem sized_insert_root()
executes __rb_insert(struct rb_node* node, struct rb_root* root,
                    void (*augment_rotate)(struct rb_node*, struct rb_node*)) {
    ensures InsertSizedRoot(&__rb_insert) as { tree: tree } by {
        step(__rb_insert(node, root, augment_rotate), { tree: tree });
        simp();
    }
}

// These wrappers accept any typed rotation pointer, including the writable
// size callback: the root-only path never calls it.
void __rb_insert_augmented(struct rb_node* node, struct rb_root* root,
                  void (*augment_rotate)(struct rb_node*, struct rb_node*)) {
    owns root->rb_node;
    owns tree: sized_at(node);
    requires root->rb_node == node;
    requires tree.model == SizedTree::Node(node, 0, Color::Red, sized_value(tree.model), sized_left(tree.model), sized_right(tree.model));
    ensures root->rb_node == node;
    ensures tree.model == sized_recolor(old(tree.model), Color::Black);
} by {
    step(__rb_insert(node, root, augment_rotate), { tree: tree });
    execute(); simp();
}

void rb_insert_augmented(struct rb_node* node, struct rb_root* root,
                  const struct rb_augment_callbacks* augment) {
    views augment->rotate;
    owns root->rb_node;
    owns tree: sized_at(node);
    requires root->rb_node == node;
    requires tree.model == SizedTree::Node(node, 0, Color::Red, sized_value(tree.model), sized_left(tree.model), sized_right(tree.model));
    ensures root->rb_node == node;
    ensures tree.model == sized_recolor(old(tree.model), Color::Black);
} by {
    step(__rb_insert_augmented(node, root, augment->rotate), { tree: tree });
    execute(); simp();
}
