verifying "rb_erase_color.c";
import "../rbtree-model/rbtree_resources.click";

void rb_set_parent(struct rb_node* rb, struct rb_node* p) {
    consumes before: rb_at(rb);
    requires rb != 0;
    requires aligned(p, 8);
    produces after: rb_at(rb);
    ensures after.model == rb_reparent(old(before.model), p);
} by {
    match before.model {
        RbTree::Empty => {
            unfold(before);
            contradiction(rb != 0);
        },
        RbTree::Node(node, parent, color, lm, rm) => {
            let { left: left, right: right } = unfold(before);
            match color {
                Color::Red => {
                    have (rb->__rb_parent_color & 1) == 0 by {
                        rewrite((rb->__rb_parent_color & 1) == color_bit(color));
                        rewrite(color == Color::Red); unfold(color_bit(Color::Red)); normalize();
                    }
                    execute();
                    have rb->__rb_parent_color == (address(p) | 0) by { simp(); }
                    have rb->__rb_parent_color == address(p) + 0 by {
                        rewrite(rb->__rb_parent_color == (address(p) | 0)); normalize();
                    }
                    have (rb->__rb_parent_color & 1) == 0 by {
                        rewrite(rb->__rb_parent_color == address(p) + 0); arithmetic() using { aligned(p, 8); }
                    }
                    have color_bit(color) == 0 by { rewrite(color == Color::Red); unfold(color_bit(Color::Red)); normalize(); }
                    let after = fold(rb_at(rb), { model: RbTree::Node(node, p, color, lm, rm) }, { left: left, right: right });
                    have after.model == rb_reparent(old(before.model), p) by {
                        rewrite(old(before.model) == RbTree::Node(node, parent, color, lm, rm));
                        unfold(rb_reparent(RbTree::Node(node, parent, color, lm, rm), p)); simp();
                    }
                    simp();
                },
                Color::Black => {
                    have (rb->__rb_parent_color & 1) == 1 by {
                        rewrite((rb->__rb_parent_color & 1) == color_bit(color));
                        rewrite(color == Color::Black); unfold(color_bit(Color::Black)); normalize();
                    }
                    execute();
                    have rb->__rb_parent_color == (1 | address(p)) by { simp(); }
                    have rb->__rb_parent_color == address(p) + 1 by {
                        rewrite(rb->__rb_parent_color == (1 | address(p))); arithmetic() using { aligned(p, 8); }
                    }
                    have (rb->__rb_parent_color & 1) == 1 by {
                        rewrite(rb->__rb_parent_color == address(p) + 1); arithmetic() using { aligned(p, 8); }
                    }
                    have color_bit(color) == 1 by { rewrite(color == Color::Black); unfold(color_bit(Color::Black)); normalize(); }
                    let after = fold(rb_at(rb), { model: RbTree::Node(node, p, color, lm, rm) }, { left: left, right: right });
                    have after.model == rb_reparent(old(before.model), p) by {
                        rewrite(old(before.model) == RbTree::Node(node, parent, color, lm, rm));
                        unfold(rb_reparent(RbTree::Node(node, parent, color, lm, rm), p)); simp();
                    }
                    simp();
                },
            }
        },
    }
}
