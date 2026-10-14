// One general contract for the unchanged Linux `rb_erase`: any node of a
// valid, parent-consistent tree.
verifying "rb_erase.c";
import "rbtree_erase_augmented.click";
import "rbtree_erase_color_flips_red_all.click";

// The tree after erase-color repair of a deficit outcome.
function erase_repaired(outcome: EraseOutcome) -> RbTree {
    match outcome {
        EraseOutcome::Balanced(t) => t,
        EraseOutcome::Deficit(c) => erase_flips_red_all_result(c, RbTree::Empty),
    }
}

void rb_erase(struct rb_node* node, struct rb_root* root) {
    consumes tree: rb_at(node);
    consumes up: ctx_at(node, root);
    requires tree.model != RbTree::Empty;
    requires is_rb(tree.model) == 1;
    requires ctx_rb(up.model, black_height(tree.model), rb_color(tree.model)) == 1;
    requires ctx_consistent(up.model, tree.model, 0) == 1;
    views dummy_callbacks.propagate;
    views dummy_callbacks.copy;
    views dummy_callbacks.rotate;
    produces node->__rb_parent_color;
    produces node->rb_left;
    produces node->rb_right;
    produces whole: rb_root_at(root);
    ensures whole.model == erase_repaired(erase_outcome(old(tree.model), old(up.model)));
    ensures is_rb_root(whole.model) == 1;
    ensures rb_tree_parent_consistent(whole.model) == 1;
    ensures rb_inorder(whole.model) == rb_inorder(plug(old(up.model), erase_splice(old(tree.model))));
    ensures rb_inorder(erase_splice(old(tree.model)))
        == list_append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model))));
} by {
    apply(dummy_propagate_contract());
    apply(dummy_copy_contract());
    apply(dummy_rotate_contract());
    fold(erase_callbacks(&dummy_callbacks));
    step(); // Declare rebalance.
    let { out: out } = step(__rb_erase_augmented(node, root, &dummy_callbacks), { tree: tree, up: up });
    match out.model {
        EraseOutcome::Balanced(t) => {
            have erase_out_rb(EraseOutcome::Balanced(t)) == 1 by { rewrite(EraseOutcome::Balanced(t) == out.model); assumption(); }
            have is_rb_root(t) == 1 by { unfold(erase_out_rb(EraseOutcome::Balanced(t))); assumption(); }
            have erase_out_tree(EraseOutcome::Balanced(t)) == t by { unfold(erase_out_tree(EraseOutcome::Balanced(t))); normalize(); }
            have rb_tree_parent_consistent(t) == 1 by {
                rewrite(t == erase_out_tree(EraseOutcome::Balanced(t))); rewrite(EraseOutcome::Balanced(t) == out.model); assumption();
            }
            have t == plug(old(up.model), erase_splice(old(tree.model))) by {
                rewrite(t == erase_out_tree(EraseOutcome::Balanced(t))); rewrite(EraseOutcome::Balanced(t) == out.model); assumption();
            }
            have erase_repaired(erase_outcome(old(tree.model), old(up.model))) == t by {
                rewrite(erase_outcome(old(tree.model), old(up.model)) == out.model);
                rewrite(out.model == EraseOutcome::Balanced(t));
                unfold(erase_repaired(EraseOutcome::Balanced(t))); normalize();
            }
            let { whole: whole } = unfold(out);
            have rebalance == 0;
            step(); // Skip repair.
            execute(); simp();
        },
        EraseOutcome::Deficit(c) => {
            have erase_out_rb(EraseOutcome::Deficit(c)) == 1 by { rewrite(EraseOutcome::Deficit(c) == out.model); assumption(); }
            have ctx_rb(c, Nat::Succ(Nat::Zero), Color::Black) == 1 by { unfold(erase_out_rb(EraseOutcome::Deficit(c))); assumption(); }
            have ctx_rb(c, Nat::Succ(black_height(RbTree::Empty)), Color::Black) == 1 by {
                unfold(black_height(RbTree::Empty)); assumption();
            }
            have erase_out_tree(EraseOutcome::Deficit(c)) == plug(c, RbTree::Empty) by {
                unfold(erase_out_tree(EraseOutcome::Deficit(c))); normalize();
            }
            have rb_tree_parent_consistent(plug(c, RbTree::Empty)) == 1 by {
                rewrite(plug(c, RbTree::Empty) == erase_out_tree(EraseOutcome::Deficit(c)));
                rewrite(EraseOutcome::Deficit(c) == out.model); assumption();
            }
            have plug(c, RbTree::Empty) == plug(old(up.model), erase_splice(old(tree.model))) by {
                rewrite(plug(c, RbTree::Empty) == erase_out_tree(EraseOutcome::Deficit(c)));
                rewrite(EraseOutcome::Deficit(c) == out.model); assumption();
            }
            have erase_repaired(erase_outcome(old(tree.model), old(up.model))) == erase_flips_red_all_result(c, RbTree::Empty) by {
                rewrite(erase_outcome(old(tree.model), old(up.model)) == out.model);
                rewrite(out.model == EraseOutcome::Deficit(c));
                unfold(erase_repaired(EraseOutcome::Deficit(c))); normalize();
            }
            let { deficit: deficit } = unfold(out);
            have rebalance != 0;
            step(); // Select the nonnull rebalance branch.
            let { whole: whole } = step(____rb_erase_color(rebalance, root, dummy_rotate), { c: deficit });
            execute(); simp();
        },
    }
}
