// Replace the focus link while preserving its surrounding context.
// Ownership of the old node's tag separates it from a nonempty sibling.
verifying "rb_erase_augmented.c";
import "../rbtree-model/rbtree_resources.click";

void __rb_change_child(struct rb_node* old, struct rb_node* new,
                       struct rb_node* parent, struct rb_root* root) {
    consumes before: ctx_at(old, root);
    owns old->__rb_parent_color;
    requires old != 0;
    requires ctx_node_is(before.model, parent) == 1;
    produces after: ctx_at(new, root);
    ensures after.model == old(before.model);
    ensures old->__rb_parent_color == old(old->__rb_parent_color);
    ensures ((old->__rb_parent_color & ~3) as (struct rb_node *))
        == old((old->__rb_parent_color & ~3) as (struct rb_node *));
} by {
    match before.model {
        Context::Top => {
            have parent == 0;
            unfold(before);
            step_until(function.exit);
            let after = fold(ctx_at(new, root), { model: Context::Top });
            solve();
        },
        Context::Left(identity, grandparent, color, sibling_model, outer_model) => {
            have parent == identity;
            let { sibling: sibling, up: outer } = unfold(before);
            mark before_child_change;
            have separate(memory(parent->rb_left), memory(identity->__rb_parent_color)) by {
                rewrite(parent == identity);
                normalize();
            }
            step_until(function.exit);
            have separate(statement(0).statement(0).statement(0).footprint, memory(identity->__rb_parent_color)) by {
                normalize() using {
                    parent == identity;
                    separate(memory(parent->rb_left), memory(identity->__rb_parent_color));
                };
            }
            have identity->__rb_parent_color == at(before_child_change, identity->__rb_parent_color) by {
                transport_certificate {
                    premise 0: separate(statement(0).statement(0).statement(0).footprint, memory(identity->__rb_parent_color))
                        => separate(statement(0).statement(0).statement(0).footprint, memory(identity->__rb_parent_color));
                    preserve 0 => identity->__rb_parent_color == at(before_child_change, identity->__rb_parent_color);
                    conclusion 1;
                }
            }
            have identity->__rb_parent_color == address(grandparent) + (identity->__rb_parent_color & 1) by {
                rewrite(identity->__rb_parent_color == at(before_child_change, identity->__rb_parent_color));
                assumption();
            }
            let after = fold(ctx_at(new, root), {
                model: Context::Left(identity, grandparent, color, sibling_model, outer_model)
            }, { up: outer });
            solve();
        },
        Context::Right(identity, grandparent, color, sibling_model, outer_model) => {
            have parent == identity;
            let { sibling: sibling, up: outer } = unfold(before);
            match sibling.model {
                RbTree::Empty => {
                    unfold(sibling);
                    mark before_child_change;
                    have separate(memory(parent->rb_right), memory(identity->__rb_parent_color)) by {
                        rewrite(parent == identity);
                        normalize();
                    }
                    step_until(function.exit);
                    have separate(statement(0).statement(0).statement(1).footprint, memory(identity->__rb_parent_color)) by {
                        normalize() using {
                            parent == identity;
                            separate(memory(parent->rb_right), memory(identity->__rb_parent_color));
                        };
                    }
                    have identity->__rb_parent_color == at(before_child_change, identity->__rb_parent_color) by {
                        transport_certificate {
                            premise 0: separate(statement(0).statement(0).statement(1).footprint, memory(identity->__rb_parent_color))
                                => separate(statement(0).statement(0).statement(1).footprint, memory(identity->__rb_parent_color));
                            preserve 0 => identity->__rb_parent_color == at(before_child_change, identity->__rb_parent_color);
                            conclusion 1;
                        }
                    }
                    have identity->__rb_parent_color == address(grandparent) + (identity->__rb_parent_color & 1) by {
                        rewrite(identity->__rb_parent_color == at(before_child_change, identity->__rb_parent_color));
                        assumption();
                    }

                    let sibling = fold(rb_at(parent->rb_left), { model: RbTree::Empty });
                    let after = fold(ctx_at(new, root), {
                        model: Context::Right(identity, grandparent, color, sibling_model, outer_model)
                    }, { up: outer });
                    solve();
                },
                RbTree::Node(sid, sp, sc, sl, sr) => {
                    let { left: left, right: right } = unfold(sibling);
                    step();
                    step();
                    let sibling = fold(rb_at(parent->rb_left), {
                        model: RbTree::Node(sid, sp, sc, sl, sr)
                    });
                    mark before_child_change;
                    have separate(memory(parent->rb_right), memory(identity->__rb_parent_color)) by {
                        rewrite(parent == identity);
                        normalize();
                    }
                    step_until(function.exit);
                    have separate(statement(0).statement(0).statement(1).footprint, memory(identity->__rb_parent_color)) by {
                        normalize() using {
                            parent == identity;
                            separate(memory(parent->rb_right), memory(identity->__rb_parent_color));
                        };
                    }
                    have identity->__rb_parent_color == at(before_child_change, identity->__rb_parent_color) by {
                        transport_certificate {
                            premise 0: separate(statement(0).statement(0).statement(1).footprint, memory(identity->__rb_parent_color))
                                => separate(statement(0).statement(0).statement(1).footprint, memory(identity->__rb_parent_color));
                            preserve 0 => identity->__rb_parent_color == at(before_child_change, identity->__rb_parent_color);
                            conclusion 1;
                        }
                    }
                    have identity->__rb_parent_color == address(grandparent) + (identity->__rb_parent_color & 1) by {
                        rewrite(identity->__rb_parent_color == at(before_child_change, identity->__rb_parent_color));
                        assumption();
                    }

                    let after = fold(ctx_at(new, root), {
                        model: Context::Right(identity, grandparent, color, sibling_model, outer_model)
                    }, { up: outer });
                    solve();
                },
            }
        },
    }
}
