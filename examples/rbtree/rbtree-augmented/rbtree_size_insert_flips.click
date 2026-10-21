arithmetic "integer";

// An owned focus and the remaining arbitrary sequence of insertion color flips.
verifying "rb_insert_augmented.c";
verifying "rbtree_size_compute.c";
verifying "rbtree_size_copy.c";
import "rbtree_size_insert_flips_model.click";

resource sized_flip_state(root: struct rb_root*) {
    field chain: SizedFlipChain;
    field model: SizedTree;
    field context: SizedContext;
    match model {
        SizedTree::Empty => { fact false; },
        SizedTree::Node(node, parent, color, value, left, right) => {
            owns root->rb_node;
            owns focus: sized_at(node);
            owns path: sized_context_at(node, root->rb_node, 0, value);
            fact focus.model == model;
            fact path.model == context;
            fact parent == sized_context_parent(context, 0);
        },
    }
}

tactic restore_sized_flip_state(root: struct rb_root*) {
    consumes state: sized_flip_state(root);
    produces root->rb_node;
    produces whole: sized_at(root->rb_node);
    ensures whole.model == sized_plug(old(state.context), old(state.model));
    ensures sized_parent_is(whole.model, 0) == 1;
} by {
    match state.model {
        SizedTree::Empty => { unfold(state); contradiction(false); },
        SizedTree::Node(node, parent, color, value, left, right) => {
            let { focus: focus, path: path } = unfold(state);
            have focus.model == old(state.model) by normalize();
            have path.model == old(state.context) by normalize();
            have sized_value(focus.model) == value by {
                rewrite(focus.model == old(state.model));
                rewrite(old(state.model) == SizedTree::Node(node, parent, color, value, left, right));
                unfold(sized_value(SizedTree::Node(node, parent, color, value, left, right)));
                normalize();
            }
            have sized_context_parent(path.model, 0) == parent by {
                rewrite(path.model == old(state.context));
                assumption();
            }
            have sized_parent_is(focus.model, sized_context_parent(path.model, 0)) == 1 by {
                rewrite(focus.model == old(state.model));
                rewrite(old(state.model) == SizedTree::Node(node, parent, color, value, left, right));
                unfold(sized_parent_is(SizedTree::Node(node, parent, color, value, left, right), sized_context_parent(path.model, 0)));
                normalize() using { sized_context_parent(path.model, 0) == parent; };
            }
            let { whole: whole } = restore_sized_context(node, root->rb_node, 0, value, { path: path, sub: focus });
            have whole.model == sized_plug(old(state.context), old(state.model));
            have sized_parent_is(whole.model, 0) == 1;
        },
    }
}
