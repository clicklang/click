// Update a packed parent word without requiring the root cache to be current.
verifying "rb_insert_augmented.c" as insert;
verifying "rbtree_size_compute.c";
verifying "rbtree_size_copy.c";
import "rbtree_size_reparent.click";
import "rbtree_size_recompute_model.click";

function sized_root_color_bit(tree: SizedTree) -> int32 {
    match tree {
        SizedTree::Empty => 0,
        SizedTree::Node(identity, parent, shade, value, left, right) => color_bit(shade),
    }
}

void insert::rb_set_parent_color(struct rb_node* rb, struct rb_node* p, int32 color) {
    consumes tree: sized_recompute_at(rb);
    produces after: sized_recompute_at(rb);
    requires rb != 0;
    requires aligned(p, 8);
    requires color == sized_root_color_bit(tree.model);
    ensures after.model == sized_reparent(old(tree.model), p);
    ensures ((rb->__rb_parent_color & ~3) as (struct rb_node *)) == p;
} by {
    match tree.model {
        SizedTree::Empty => {
            unfold(tree);
            contradiction(rb != 0);
        },
        SizedTree::Node(identity, before, shade, value, left_model, right_model) => {
            have color == color_bit(shade) by {
                rewrite(color, sized_root_color_bit(tree.model));
                rewrite(tree.model, SizedTree::Node(identity, before, shade, value, left_model, right_model));
                unfold(sized_root_color_bit(SizedTree::Node(identity, before, shade, value, left_model, right_model)));
                normalize();
            }
            match shade {
                Color::Black => {
                    have color == 1 by {
                        rewrite(color, color_bit(shade));
                        rewrite(shade, Color::Black);
                        unfold(color_bit(Color::Black)); normalize();
                    }
                    let { metadata: metadata, left: left, right: right } = unfold(tree);
                    have 0 <= color by { rewrite(color, 1); normalize(); }
                    have color <= 1 by { rewrite(color, 1); normalize(); }
                    step();
                    have rb->__rb_parent_color == address(p) + 1 by {
                        rewrite(color, 1);
                        close() using { aligned(p, 8); };
                    }
                    have (rb->__rb_parent_color & ~3) == address(p) by {
                        rewrite(color, 1);
                        close() using { aligned(p, 8); };
                    }
                    have ((rb->__rb_parent_color & ~3) as (struct rb_node *)) == p by {
                        close();
                    }
                    have (rb->__rb_parent_color & 1) == 1 by {
                        rewrite(rb->__rb_parent_color, address(p) + 1);
                        close() using { aligned(p, 8); };
                    }
                    have rb->__rb_parent_color == address(p) + (rb->__rb_parent_color & 1) by {
                        rewrite((rb->__rb_parent_color & 1), 1);
                        close();
                    }
                    unfold(color_bit(Color::Black));
                    let after = fold(sized_recompute_at(rb), {
                        model: SizedTree::Node(identity, p, Color::Black, value, left_model, right_model),
                        metadata: metadata, left: left, right: right
                    });
                    unfold(sized_reparent(SizedTree::Node(identity, before, shade, value, left_model, right_model), p));
                    step_until(function.exit);
                },
                Color::Red => {
                    have color == 0 by {
                        rewrite(color, color_bit(shade));
                        rewrite(shade, Color::Red);
                        unfold(color_bit(Color::Red)); normalize();
                    }
                    let { metadata: metadata, left: left, right: right } = unfold(tree);
                    have 0 <= color by { rewrite(color, 0); normalize(); }
                    have color <= 1 by { rewrite(color, 0); normalize(); }
                    step();
                    have rb->__rb_parent_color == address(p) + 0 by {
                        rewrite(color, 0); normalize();
                    }
                    have (rb->__rb_parent_color & ~3) == address(p) by {
                        rewrite(color, 0);
                        close() using { aligned(p, 8); };
                    }
                    have ((rb->__rb_parent_color & ~3) as (struct rb_node *)) == p by {
                        close();
                    }
                    have (rb->__rb_parent_color & 1) == 0 by {
                        rewrite(rb->__rb_parent_color, address(p) + 0);
                        close() using { aligned(p, 8); };
                    }
                    have rb->__rb_parent_color == address(p) + (rb->__rb_parent_color & 1) by {
                        rewrite((rb->__rb_parent_color & 1), 0);
                        close();
                    }
                    unfold(color_bit(Color::Red));
                    let after = fold(sized_recompute_at(rb), {
                        model: SizedTree::Node(identity, p, Color::Red, value, left_model, right_model),
                        metadata: metadata, left: left, right: right
                    });
                    unfold(sized_reparent(SizedTree::Node(identity, before, shade, value, left_model, right_model), p));
                    step_until(function.exit);
                },
            }
        },
    }
}
