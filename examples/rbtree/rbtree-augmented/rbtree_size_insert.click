// Root-only insertion boundary: no rotation callback is invoked.
// The child subtrees may be nonempty; their cached sizes remain owned and valid.
verifying "rb_insert_augmented.c";
verifying "rbtree_size_copy.c";
verifying "rbtree_size_compute.c";
import "rbtree_size_recolor.click";

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
        rewrite((node->__rb_parent_color & 1), color_bit(Color::Red));
        rewrite(color_bit(Color::Red), 0);
        known();
    }
    have node->__rb_parent_color == 0 by {
        rewrite(node->__rb_parent_color, address(0) + (node->__rb_parent_color & 1));
        rewrite((node->__rb_parent_color & 1), 0);
        known();
    }
    step_until(loop(0).entry);
    have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == 0 by {
        rewrite(node->__rb_parent_color, 0u64);
        known();
    }
    let tree = fold(sized_at(node), { model: old(tree.model), metadata: metadata, left: left, right: right }) {
        requires sized_parent_is(sized_left(old(tree.model)), node) == 1 by known();
        requires sized_parent_is(sized_right(old(tree.model)), node) == 1 by known();
        requires to_integer(sized_value(old(tree.model))) ==
            1 + to_integer(sized_value(sized_left(old(tree.model)))) +
                to_integer(sized_value(sized_right(old(tree.model)))) by known();
    };
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
        initialize by solve();
        maintain by {
            let { metadata: metadata, left: left, right: right } = unfold(tree);
            step(); step();
            have node->__rb_parent_color == 1 by known();
            have (node->__rb_parent_color & 1) == color_bit(Color::Black) by {
                rewrite(node->__rb_parent_color, 1u64);
                unfold(color_bit(Color::Black));
                known();
            }
            have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == 0 by {
                rewrite(node->__rb_parent_color, 1u64);
                known();
            }
            let tree = fold(sized_at(node), {
                model: SizedTree::Node(node, parent, Color::Black, sized_value(old(tree.model)), sized_left(old(tree.model)), sized_right(old(tree.model))),
                metadata: metadata, left: left, right: right
            }) {
                requires aligned(parent, 8) by known();
                requires node->__rb_parent_color == address(parent) + (node->__rb_parent_color & 1) by known();
            };
            have sized_recolor(old(tree.model), Color::Black) == tree.model by {
                rewrite(parent, 0);
                rewrite(sized_recolor(old(tree.model), Color::Black),
                    sized_recolor(SizedTree::Node(node, 0, Color::Red, sized_value(old(tree.model)), sized_left(old(tree.model)), sized_right(old(tree.model))), Color::Black));
                unfold(sized_recolor(SizedTree::Node(node, 0, Color::Red, sized_value(old(tree.model)), sized_left(old(tree.model)), sized_right(old(tree.model))), Color::Black));
            }
            step();
        }
    }
    have node == old(node) by { known(); }
}

theorem sized_insert_root()
executes __rb_insert(struct rb_node* node, struct rb_root* root,
                    void (*augment_rotate)(struct rb_node*, struct rb_node*)) {
    ensures InsertSizedRoot(&__rb_insert) as { tree: tree } by {
        step(__rb_insert, { tree: tree });
        solve();
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
    step(__rb_insert, { tree: tree });
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
    step(__rb_insert_augmented, { tree: tree });
}
