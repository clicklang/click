import click::integer;

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
            step_until(function.exit);
            have (address(p) & 7u64) == 0u64 by close();
            apply(integer::uint64_mask_subset(address(p), 7u64, 1u64));
            have rb->__rb_parent_color == ((old(rb->__rb_parent_color) & 1u64) | address(p)) by close();
            apply(integer::uint64_and_or(old(rb->__rb_parent_color) & 1u64, address(p), 1u64));
            apply(integer::uint64_and_associate(old(rb->__rb_parent_color), 1u64, 1u64));
            have (1u64 & 1u64) == 1u64 by close();
            have ((old(rb->__rb_parent_color) & 1u64) & 1u64) == (old(rb->__rb_parent_color) & 1u64) by {
                rewrite(((old(rb->__rb_parent_color) & 1u64) & 1u64), (old(rb->__rb_parent_color) & (1u64 & 1u64)));
                rewrite(1u64 & 1u64, 1u64);
                close();
            }
            apply(integer::uint64_or_zero(old(rb->__rb_parent_color) & 1u64));
            have (rb->__rb_parent_color & 1u64) == (old(rb->__rb_parent_color) & 1u64) by {
                rewrite(rb->__rb_parent_color, ((old(rb->__rb_parent_color) & 1u64) | address(p)));
                rewrite((((old(rb->__rb_parent_color) & 1u64) | address(p)) & 1u64),
                        (((old(rb->__rb_parent_color) & 1u64) & 1u64) | (address(p) & 1u64)));
                rewrite(((old(rb->__rb_parent_color) & 1u64) & 1u64), (old(rb->__rb_parent_color) & 1u64));
                rewrite(address(p) & 1u64, 0u64);
                close();
            }
            have (rb->__rb_parent_color & 1u64) == color_bit(color) by {
                rewrite(rb->__rb_parent_color & 1u64, old(rb->__rb_parent_color) & 1u64);
                close();
            }
            apply(integer::uint64_or_masked(address(p), old(rb->__rb_parent_color), 1u64));
            apply(integer::uint64_or_commute(old(rb->__rb_parent_color) & 1u64, address(p)));
            have rb->__rb_parent_color == address(p) + (rb->__rb_parent_color & 1) by {
                rewrite(rb->__rb_parent_color & 1u64, old(rb->__rb_parent_color) & 1u64);
                rewrite(rb->__rb_parent_color, ((old(rb->__rb_parent_color) & 1u64) | address(p)));
                rewrite(((old(rb->__rb_parent_color) & 1u64) | address(p)), (address(p) | (old(rb->__rb_parent_color) & 1u64)));
                close();
            }
            let after = fold(rb_at(rb), { model: RbTree::Node(node, p, color, lm, rm), left: left, right: right });
            have after.model == rb_reparent(old(before.model), p) by {
                rewrite(before.model, RbTree::Node(node, parent, color, lm, rm));
                unfold(rb_reparent(old(RbTree::Node(node, parent, color, lm, rm)), p));
                normalize() using {};
            }
            close();
        },
    }
}
