verifying "rb_insert_augmented.c" as insert;

resource sized_root_rotation_parent_word(node: struct rb_node*, parent: struct rb_node*) {
    field bits: uint64;
    owns node->__rb_parent_color;
    fact node->__rb_parent_color == bits;
    fact ((node->__rb_parent_color & ~3) as (struct rb_node *)) == parent;
}

// Keep both complete parent words across the root-link store.
void insert::__rb_rotate_set_parents(struct rb_node* old, struct rb_node* new,
                            struct rb_root* root, int32 color) {
    owns old->__rb_parent_color;
    owns new->__rb_parent_color;
    owns root->rb_node;
    requires old != 0;
    requires new != 0;
    requires aligned(new, 8);
    requires old->__rb_parent_color == 1;
    requires color == 0;
    ensures old->__rb_parent_color == address(new);
    ensures ((old->__rb_parent_color & ~3) as (struct rb_node *)) == new;
    ensures new->__rb_parent_color == 1;
    ensures root->rb_node == new;
} by {
    have 0 <= color by { rewrite(color, 0); normalize(); }
    have color <= 1 by { rewrite(color, 0); normalize(); }
    step(); step(); step(); // Assign the result of rb_parent to parent.
    have parent == 0 by { normalize(); }
    step();
    have new->__rb_parent_color == 1 by { close(); }
    have ((new->__rb_parent_color & ~3) as (struct rb_node *)) == 0 by {
        rewrite(new->__rb_parent_color, 1); normalize();
    }
    let promoted = fold(sized_root_rotation_parent_word(new, 0), { bits: 1u64 });
    step();
    have old->__rb_parent_color == (address(new) | color) by { close(); }
    have old->__rb_parent_color == address(new) by {
        rewrite(old->__rb_parent_color, (address(new) | color));
        rewrite(color, 0); normalize();
    }
    have (old->__rb_parent_color & ~3) == address(new) by {
        rewrite(old->__rb_parent_color, address(new));
        close() using { aligned(new, 8); };
    }
    have ((old->__rb_parent_color & ~3) as (struct rb_node *)) == new by { close(); }
    let demoted = fold(sized_root_rotation_parent_word(old, new), { bits: address(new) });
    step();
    unfold(demoted);
    unfold(promoted);
    step_until(function.exit);
}
