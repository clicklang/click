// Arbitrarily many insertion color flips, ending at the root or a black parent.
verifying "rb_insert_augmented.c" as insert;
verifying "rbtree_size_compute.c";
verifying "rbtree_size_copy.c";
import click::integer;
import "rbtree_size_insert_flips.click";
import "rbtree_size_context_flip_frames.click";

// Retain complete node observations through read-only C steps.
resource sized_flip_chain_node_frame(p: struct rb_node*, up: struct rb_node*) {
    field color: Color;
    field word: uint64;
    field left: int32*;
    field right: int32*;
    owns p->__rb_parent_color;
    fact p->__rb_parent_color == word;
    fact p->__rb_parent_color == address(up) + (p->__rb_parent_color & 1);
    fact ((p->__rb_parent_color & ~3) as (struct rb_node*)) == up;
    fact (p->__rb_parent_color & 1) == color_bit(color);
    owns p->rb_left;
    owns p->rb_right;
    fact p->rb_left == left;
    fact p->rb_right == right;
    fact p->rb_left != p;
    fact p->rb_right != p;
}

resource sized_flip_red_word(node: struct rb_node*) {
    field word: uint64;
    owns node->__rb_parent_color;
    fact node->__rb_parent_color == word;
    fact (node->__rb_parent_color & 1) == 0;
}

resource sized_flip_chain_root_link(root: struct rb_root*) {
    field node: int32*;
    owns root->rb_node;
    fact root->rb_node == node;
}

// Track the root link alongside the loop focus and its ancestor path.
resource sized_flip_chain_at(root: struct rb_root*) {
    field root_node: int32*;
    field chain: SizedFlipChain;
    field model: SizedTree;
    field context: SizedContext;
    match model {
        SizedTree::Empty => { fact false; },
        SizedTree::Node(node, parent, shade, value, left, right) => {
            owns root->rb_node;
            owns focus: sized_at(node);
            owns path: sized_context_at(node, root->rb_node, 0, value);
            fact focus.model == model;
            fact path.model == context;
            fact parent == sized_context_parent(context, 0);
            fact root->rb_node == root_node;
        },
    }
}

function sized_flip_chain_node(node: struct rb_node*) -> int32 { 1 }

resource sized_flip_chain_grand_word(p: struct rb_node*) {
    field up: int32*;
    field word: uint64;
    owns p->__rb_parent_color;
    fact p->__rb_parent_color == word;
    fact ((p->__rb_parent_color & ~3) as (struct rb_node*)) == up;
    fact sized_flip_chain_node(up) == 1;
}

// The packed word already identifies a typed parent, possibly null.
struct rb_node* insert::rb_parent(struct rb_node* r) {
    consumes word: sized_flip_chain_grand_word(r);
    produces kept: sized_flip_chain_grand_word(r);
    ensures kept.up == old(word.up);
    ensures kept.word == old(word.word);
    ensures result == old(word.up);
    ensures result != 0 implies sized_flip_chain_node(result) == 1;
} by {
    unfold(word);
    step_until(function.exit);
    let kept = fold(sized_flip_chain_grand_word(r), { up: old(word.up), word: old(word.word) });
}

void insert::__rb_insert(struct rb_node* node, struct rb_root* root,
                 void (*augment_rotate)(struct rb_node*, struct rb_node*)) {
    consumes state: sized_flip_chain_at(root);
    requires sized_flip_allowed(state.chain) == 1;
    requires state.context == sized_flip_context(state.chain);
    requires node == sized_flip_node(state.model);
    requires sized_flip_color(state.model) == 0;
    produces root->rb_node;
    produces whole: sized_at(old(root->rb_node));
    requires node->rb_left != node;
    requires node->rb_right != node;
    ensures root->rb_node == old(root->rb_node);
    ensures whole.model == sized_flip_result(old(state.chain), old(state.model));
    ensures sized_parent_is(whole.model, 0) == 1;
} by {
    match state.model {
        SizedTree::Empty => { unfold(state); contradiction(); },
        SizedTree::Node(identity, ancestor, shade, value, left, right) => {
            have node == identity by {
                rewrite(node, sized_flip_node(state.model));
                rewrite(state.model, SizedTree::Node(identity, ancestor, shade, value, left, right));
                unfold(sized_flip_node(SizedTree::Node(identity, ancestor, shade, value, left, right))); close();
            }
            have color_bit(shade) == 0 by {
                unfold(sized_flip_color(SizedTree::Node(identity, ancestor, shade, value, left, right)));
                rewrite(color_bit(shade), sized_flip_color(SizedTree::Node(identity, ancestor, shade, value, left, right)));
                rewrite(SizedTree::Node(identity, ancestor, shade, value, left, right), state.model); close();
            }
            let { focus: focus, path: path } = unfold(state);
            let { metadata: metadata, left: l, right: r } = unfold(focus);
            have identity->__rb_parent_color == address(ancestor) by {
                rewrite(identity->__rb_parent_color, address(ancestor) + (identity->__rb_parent_color & 1));
                rewrite((identity->__rb_parent_color & 1), color_bit(shade));
                rewrite(color_bit(shade), 0); close();
            }
            have node->__rb_parent_color == address(ancestor) by {
                rewrite(node, identity);
                close();
            }
            have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == ancestor by {
                rewrite(node, identity);
                close();
            }
            have ancestor == sized_context_parent(old(state.context), 0) by close();
            let entry_link = fold(sized_flip_chain_root_link(root), { node: old(root->rb_node) });
            let entry_focus = fold(sized_flip_chain_node_frame(node, ancestor), {
                color: shade, word: node->__rb_parent_color, left: node->rb_left, right: node->rb_right
            });
            step(); step(); step(); step();
            unfold(entry_focus); unfold(entry_link);
            have root->rb_node == old(root->rb_node) by close();
            let focus = fold(sized_at(node), { model: SizedTree::Node(identity, ancestor, shade, value, left, right), metadata: metadata, left: l, right: r });
            let state = fold(sized_flip_chain_at(root), { root_node: old(root->rb_node), chain: old(state.chain), model: SizedTree::Node(identity, ancestor, shade, value, left, right), context: old(state.context), focus: focus, path: path });
            apply(sized_flip_context_parent(state.chain));
            apply(sized_flip_depth_nonnegative(state.chain));
            have parent == sized_flip_parent(state.chain) by {
                rewrite(parent, ancestor);
                rewrite(ancestor, sized_context_parent(state.context, 0));
                rewrite(state.context, sized_flip_context(state.chain)); close();
            }
            step(); // Declare tmp before the loop.
            loop {
                owns state: sized_flip_chain_at(root);
                decreases sized_flip_depth(state.chain);
                invariant state.root_node == old(root->rb_node);
                invariant sized_flip_allowed(state.chain) == 1;
                invariant state.context == sized_flip_context(state.chain);
                invariant node == sized_flip_node(state.model);
                invariant sized_flip_color(state.model) == 0;
                invariant parent == sized_flip_parent(state.chain);
                invariant sized_flip_result(state.chain, state.model) == sized_flip_result(old(state.chain), old(state.model));
                initialize by close();
                maintain by {
                    mark iteration;
                    match state.model {
                        SizedTree::Empty => { unfold(state); contradiction(); },
                        SizedTree::Node(current, above, red, count, lo, hi) => {
                            have node == current by {
                                rewrite(node, sized_flip_node(state.model));
                                rewrite(state.model, SizedTree::Node(current, above, red, count, lo, hi));
                                unfold(sized_flip_node(SizedTree::Node(current, above, red, count, lo, hi))); close();
                            }
                            have color_bit(red) == 0 by {
                                unfold(sized_flip_color(SizedTree::Node(current, above, red, count, lo, hi)));
                                rewrite(color_bit(red), sized_flip_color(SizedTree::Node(current, above, red, count, lo, hi)));
                                rewrite(SizedTree::Node(current, above, red, count, lo, hi), state.model); close();
                            }
                            let { focus: focus, path: path } = unfold(state);
                            have root->rb_node == old(root->rb_node) by close();
                            apply(sized_flip_context_parent(at(iteration,state.chain)));
                            have parent == above by {
                                rewrite(parent, sized_flip_parent(at(iteration,state.chain)));
                                rewrite(sized_flip_parent(at(iteration,state.chain)), sized_context_parent(sized_flip_context(at(iteration,state.chain)),0));
                                rewrite(sized_flip_context(at(iteration,state.chain)), at(iteration,state.context)); close();
                            }
                            match at(iteration,state.chain) {
                                SizedFlipChain::LL(p, g, pv, gv, other, uncle, up) => {
                                    have path.model == SizedContext::Left(p, g, Color::Red, pv, other, SizedContext::Left(g, sized_flip_parent(up), Color::Black, gv, uncle, sized_flip_context(up))) by {
                                        rewrite(path.model, at(iteration,state.context));
                                        rewrite(at(iteration,state.context), sized_flip_context(at(iteration,state.chain)));
                                        rewrite(at(iteration,state.chain), SizedFlipChain::LL(p, g, pv, gv, other, uncle, up));
                                        unfold(sized_flip_context(SizedFlipChain::LL(p, g, pv, gv, other, uncle, up))); close();
                                    }
                                    let { metadata: p_size, sibling: other_tree, up: g_path } = unfold(path);
                                    let { metadata: g_size, sibling: uncle_tree, up: outer_path } = unfold(g_path);
                                    have parent == p by {
                                        rewrite(parent, sized_flip_parent(at(iteration,state.chain)));
                                        rewrite(at(iteration,state.chain), SizedFlipChain::LL(p, g, pv, gv, other, uncle, up));
                                        unfold(sized_flip_parent(SizedFlipChain::LL(p, g, pv, gv, other, uncle, up))); close();
                                    }
                                    match uncle {
                                        SizedTree::Empty => {
                                            unfold(sized_flip_allowed(SizedFlipChain::LL(p, g, pv, gv, other, uncle, up)));
                                            unfold(sized_flip_uncle_red(SizedTree::Empty));
                                            have sized_flip_allowed(SizedFlipChain::LL(p, g, pv, gv, other, uncle, up)) == 0 by { rewrite(uncle, SizedTree::Empty); unfold(sized_flip_allowed(SizedFlipChain::LL(p, g, pv, gv, other, SizedTree::Empty, up))); unfold(sized_flip_uncle_red(SizedTree::Empty)); close(); }
                                            have not (sized_flip_allowed(at(iteration,state.chain)) == 1) by {
                                                rewrite(at(iteration,state.chain), SizedFlipChain::LL(p, g, pv, gv, other, uncle, up));
                                                rewrite(sized_flip_allowed(SizedFlipChain::LL(p, g, pv, gv, other, uncle, up)), 0); close();
                                            }
                                            contradiction(sized_flip_allowed(at(iteration,state.chain)) == 1);
                                        },
                                        SizedTree::Node(u, ug, uc, uv, ul, ur) => {
                                            match uc {
                                                Color::Black => {
                                                    unfold(sized_flip_allowed(SizedFlipChain::LL(p, g, pv, gv, other, uncle, up)));
                                                    unfold(sized_flip_uncle_red(SizedTree::Node(u, ug, uc, uv, ul, ur)));
                                                    have sized_flip_allowed(SizedFlipChain::LL(p, g, pv, gv, other, uncle, up)) == 0 by { rewrite(uncle, SizedTree::Node(u, ug, uc, uv, ul, ur)); rewrite(uc, Color::Black); unfold(sized_flip_allowed(SizedFlipChain::LL(p, g, pv, gv, other, SizedTree::Node(u, ug, Color::Black, uv, ul, ur), up))); unfold(sized_flip_uncle_red(SizedTree::Node(u, ug, Color::Black, uv, ul, ur))); close(); }
                                                    have not (sized_flip_allowed(at(iteration,state.chain)) == 1) by {
                                                        rewrite(at(iteration,state.chain), SizedFlipChain::LL(p, g, pv, gv, other, uncle, up));
                                                        rewrite(sized_flip_allowed(SizedFlipChain::LL(p, g, pv, gv, other, uncle, up)), 0); close();
                                                    }
                                                    contradiction(sized_flip_allowed(at(iteration,state.chain)) == 1);
                                                },
                                                Color::Red => {
                                                    unfold(sized_flip_allowed(SizedFlipChain::LL(p, g, pv, gv, other, uncle, up)));
                                                    unfold(sized_flip_uncle_red(SizedTree::Node(u, ug, uc, uv, ul, ur)));
                                                    have sized_flip_allowed(SizedFlipChain::LL(p, g, pv, gv, other, uncle, up)) == sized_flip_allowed(up) by {
                                                        rewrite(uncle, SizedTree::Node(u, ug, uc, uv, ul, ur)); rewrite(uc, Color::Red);
                                                        unfold(sized_flip_allowed(SizedFlipChain::LL(p, g, pv, gv, other, SizedTree::Node(u, ug, Color::Red, uv, ul, ur), up)));
                                                        unfold(sized_flip_uncle_red(SizedTree::Node(u, ug, Color::Red, uv, ul, ur))); close();
                                                    }
                                                    have sized_flip_allowed(up) == 1 by close();
                                                    let { metadata: u_size, left: u_left, right: u_right } = unfold(uncle_tree);
                                                    have ug == g by {
                                                        if ug == g { close(); } else {
                                                            have sized_parent_is(uncle,g) == 0 by {
                                                                rewrite(uncle, SizedTree::Node(u, ug, uc, uv, ul, ur));
                                                                unfold(sized_parent_is(SizedTree::Node(u, ug, uc, uv, ul, ur),g));
                                                                close() using { not (ug == g); };
                                                            }
                                                            have not (sized_parent_is(uncle,g) == 1) by {
                                                                rewrite(sized_parent_is(uncle,g), 0); close();
                                                            }
                                                            contradiction(sized_parent_is(uncle,g) == 1);
                                                        }
                                                    }
                                                    have separate(memory(p->__rb_parent_color), memory(u->__rb_parent_color)) by close();
                                                    have p != u by close();
                                                    unfold(color_bit(Color::Red)); unfold(color_bit(Color::Black));
                                                    have (u->__rb_parent_color & 1) == 0 by {
                                                        rewrite((u->__rb_parent_color & 1), color_bit(uc));
                                                        rewrite(uc, Color::Red);
                                                        unfold(color_bit(Color::Red)); close();
                                                    }
                                                    have p->__rb_parent_color == address(g) by {
                                                        rewrite(p->__rb_parent_color, address(g) + (p->__rb_parent_color & 1));
                                                        rewrite((p->__rb_parent_color & 1), color_bit(Color::Red));
                                                        rewrite(color_bit(Color::Red), 0); close();
                                                    }
                                                    let links = fold(sized_context_flip_links(root, g, p, u), {
                                                        top: old(root->rb_node), xl: g->rb_left, xr: g->rb_right,
                                                        yl: p->rb_left, yr: p->rb_right, zl: u->rb_left, zr: u->rb_right
                                                    });
                                                    let red_uncle = fold(sized_flip_red_word(u), { word: u->__rb_parent_color });
                                                    unfold(sized_flip_chain_node(sized_flip_parent(up)));
                                                    let grand_word = fold(sized_flip_chain_grand_word(g), {
                                                        up: sized_flip_parent(up), word: g->__rb_parent_color
                                                    });
                                                    have aligned(g, 8) by close();
                                                    step(); step(); step(); step(); step(); step();
                                                    have gparent == g by close();
                                                    have aligned(gparent, 8) by close();
                                                    have (address(gparent) | 1) == address(gparent) + 1 by {
                                                        close() using { aligned(gparent, 8); };
                                                    }
                                                    step(); // Load the grandparent's right child.
                                                    have tmp == u by close();
                                                    have parent != tmp by close();
                                                    step();
                                                    unfold(red_uncle);
                                                    have (u->__rb_parent_color & 1) == 0 by close();
                                                    have (tmp->__rb_parent_color & 1) == 0 by {
                                                        close() using { tmp == u; (u->__rb_parent_color & 1) == 0; };
                                                    }
                                                    step();
                                                    step();
                                                    let uncle_word = fold(sized_context_flip_black_word(tmp, gparent), { word: tmp->__rb_parent_color });
                                                    step();
                                                    let parent_word = fold(sized_context_flip_black_word(parent, gparent), { word: parent->__rb_parent_color });
                                                    step();
                                                    let { kept: grand_word } = step(insert::rb_parent, { word: grand_word });
                                                    step();
                                                    unfold(grand_word);
                                                    have node == g by close();
                                                    have parent == sized_flip_parent(up) by close();
                                                    have aligned(parent, 8) by close();
                                                    step();
                                                    unfold(uncle_word); unfold(parent_word); unfold(links);
                                                    have g->__rb_parent_color == address(parent) by close();
                                                    have (address(parent) & 7u64) == 0u64 by {
                                                        close() using { aligned(parent, 8); };
                                                    }
                                                    have (7u64 & 1u64) == 1u64 by close();
                                                    apply(integer::uint64_mask_subset(address(parent), 7u64, 1u64));
                                                    have (g->__rb_parent_color & 1) == color_bit(Color::Red) by {
                                                        rewrite(g->__rb_parent_color, address(parent));
                                                        rewrite(color_bit(Color::Red), 0); close();
                                                    }
                                                    have g->__rb_parent_color == address(sized_flip_parent(up)) + (g->__rb_parent_color & 1) by {
                                                        rewrite(g->__rb_parent_color, address(parent));
                                                        rewrite(sized_flip_parent(up), parent);
                                                        rewrite((address(parent) & 1u64), 0u64); close();
                                                    }
                                                    have root->rb_node == old(root->rb_node) by close();
                                                    let uncle_tree = fold(sized_at(u), {
                                                        model: SizedTree::Node(u, g, Color::Black, uv, ul, ur), metadata: u_size, left: u_left, right: u_right
                                                    });
                                                    have sized_parent_is(at(iteration,state.model), p) == 1 by {
                                                        rewrite(at(iteration,state.model), SizedTree::Node(current, above, red, count, lo, hi));
                                                        unfold(sized_parent_is(SizedTree::Node(current, above, red, count, lo, hi),p));
                                                        close() using { above == p; };
                                                    }
                                                    unfold(sized_value(at(iteration,state.model)));
                                                    have to_integer(pv) == 1 + to_integer(sized_value(at(iteration,state.model))) + to_integer(sized_value(other)) by {
                                                        rewrite(at(iteration,state.model), SizedTree::Node(current, above, red, count, lo, hi));
                                                        unfold(sized_value(SizedTree::Node(current, above, red, count, lo, hi))); close();
                                                    }
                                                    let parent_tree = fold(sized_at(p), { model: SizedTree::Node(p, g, Color::Black, pv, at(iteration,state.model), other), metadata: p_size, left: focus, right: other_tree });
                                                    unfold(sized_parent_is(SizedTree::Node(p, g, Color::Black, pv, at(iteration,state.model), other), g));
                                                    unfold(sized_value(SizedTree::Node(p, g, Color::Black, pv, at(iteration,state.model), other)));
                                                    unfold(sized_parent_is(SizedTree::Node(u, g, Color::Black, uv, ul, ur), g));
                                                    unfold(sized_value(SizedTree::Node(u, g, Color::Black, uv, ul, ur)));
                                                    unfold(sized_value(SizedTree::Node(u, ug, uc, uv, ul, ur)));
                                                    have sized_value(uncle) == uv by {
                                                        rewrite(uncle, SizedTree::Node(u, ug, uc, uv, ul, ur));
                                                        unfold(sized_value(SizedTree::Node(u, ug, uc, uv, ul, ur))); close();
                                                    }
                                                    let focus = fold(sized_at(g), { model: SizedTree::Node(g, sized_flip_parent(up), Color::Red, gv, SizedTree::Node(p, g, Color::Black, pv, at(iteration,state.model), other), SizedTree::Node(u, g, Color::Black, uv, ul, ur)), metadata: g_size, left: parent_tree, right: uncle_tree });
                                                    apply(sized_flip_context_parent(up));
                                                    let state = fold(sized_flip_chain_at(root), { root_node: old(root->rb_node), chain: up, model: SizedTree::Node(g, sized_flip_parent(up), Color::Red, gv, SizedTree::Node(p, g, Color::Black, pv, at(iteration,state.model), other), SizedTree::Node(u, g, Color::Black, uv, ul, ur)), context: sized_flip_context(up), focus: focus, path: outer_path });
                                                    unfold(sized_flip_result(SizedFlipChain::LL(p, g, pv, gv, other, uncle, up), at(iteration,state.model)));
                                                    unfold(sized_recolor(SizedTree::Node(u, ug, uc, uv, ul, ur),Color::Black));
                                                    have sized_flip_result(state.chain,state.model) == sized_flip_result(old(state.chain),old(state.model)) by close();
                                                    apply(sized_flip_depth_nonnegative(up));
                                                    unfold(sized_flip_depth(SizedFlipChain::LL(p, g, pv, gv, other, uncle, up)));
                                                    have sized_flip_depth(state.chain) < sized_flip_depth(at(iteration,state.chain)) by {
                                                        rewrite(state.chain, up);
                                                        rewrite(at(iteration,state.chain), SizedFlipChain::LL(p, g, pv, gv, other, uncle, up));
                                                        unfold(sized_flip_depth(SizedFlipChain::LL(p, g, pv, gv, other, uncle, up))); close() using {};
                                                    }
                                                    unfold(sized_flip_node(SizedTree::Node(g, sized_flip_parent(up), Color::Red, gv, SizedTree::Node(p, g, Color::Black, pv, at(iteration,state.model), other), SizedTree::Node(u, g, Color::Black, uv, ul, ur))));
                                                    unfold(sized_flip_color(SizedTree::Node(g, sized_flip_parent(up), Color::Red, gv, SizedTree::Node(p, g, Color::Black, pv, at(iteration,state.model), other), SizedTree::Node(u, g, Color::Black, uv, ul, ur))));
                                                    step();
                                                },
                                            }
                                        },
                                    }
                                },
                                SizedFlipChain::LR(p, g, pv, gv, other, uncle, up) => {
                                    have path.model == SizedContext::Right(p, g, Color::Red, pv, other, SizedContext::Left(g, sized_flip_parent(up), Color::Black, gv, uncle, sized_flip_context(up))) by {
                                        rewrite(path.model, at(iteration,state.context));
                                        rewrite(at(iteration,state.context), sized_flip_context(at(iteration,state.chain)));
                                        rewrite(at(iteration,state.chain), SizedFlipChain::LR(p, g, pv, gv, other, uncle, up));
                                        unfold(sized_flip_context(SizedFlipChain::LR(p, g, pv, gv, other, uncle, up))); close();
                                    }
                                    let { metadata: p_size, sibling: other_tree, up: g_path } = unfold(path);
                                    let { metadata: g_size, sibling: uncle_tree, up: outer_path } = unfold(g_path);
                                    have parent == p by {
                                        rewrite(parent, sized_flip_parent(at(iteration,state.chain)));
                                        rewrite(at(iteration,state.chain), SizedFlipChain::LR(p, g, pv, gv, other, uncle, up));
                                        unfold(sized_flip_parent(SizedFlipChain::LR(p, g, pv, gv, other, uncle, up))); close();
                                    }
                                    match uncle {
                                        SizedTree::Empty => {
                                            unfold(sized_flip_allowed(SizedFlipChain::LR(p, g, pv, gv, other, uncle, up)));
                                            unfold(sized_flip_uncle_red(SizedTree::Empty));
                                            have sized_flip_allowed(SizedFlipChain::LR(p, g, pv, gv, other, uncle, up)) == 0 by { rewrite(uncle, SizedTree::Empty); unfold(sized_flip_allowed(SizedFlipChain::LR(p, g, pv, gv, other, SizedTree::Empty, up))); unfold(sized_flip_uncle_red(SizedTree::Empty)); close(); }
                                            have not (sized_flip_allowed(at(iteration,state.chain)) == 1) by {
                                                rewrite(at(iteration,state.chain), SizedFlipChain::LR(p, g, pv, gv, other, uncle, up));
                                                rewrite(sized_flip_allowed(SizedFlipChain::LR(p, g, pv, gv, other, uncle, up)), 0); close();
                                            }
                                            contradiction(sized_flip_allowed(at(iteration,state.chain)) == 1);
                                        },
                                        SizedTree::Node(u, ug, uc, uv, ul, ur) => {
                                            match uc {
                                                Color::Black => {
                                                    unfold(sized_flip_allowed(SizedFlipChain::LR(p, g, pv, gv, other, uncle, up)));
                                                    unfold(sized_flip_uncle_red(SizedTree::Node(u, ug, uc, uv, ul, ur)));
                                                    have sized_flip_allowed(SizedFlipChain::LR(p, g, pv, gv, other, uncle, up)) == 0 by { rewrite(uncle, SizedTree::Node(u, ug, uc, uv, ul, ur)); rewrite(uc, Color::Black); unfold(sized_flip_allowed(SizedFlipChain::LR(p, g, pv, gv, other, SizedTree::Node(u, ug, Color::Black, uv, ul, ur), up))); unfold(sized_flip_uncle_red(SizedTree::Node(u, ug, Color::Black, uv, ul, ur))); close(); }
                                                    have not (sized_flip_allowed(at(iteration,state.chain)) == 1) by {
                                                        rewrite(at(iteration,state.chain), SizedFlipChain::LR(p, g, pv, gv, other, uncle, up));
                                                        rewrite(sized_flip_allowed(SizedFlipChain::LR(p, g, pv, gv, other, uncle, up)), 0); close();
                                                    }
                                                    contradiction(sized_flip_allowed(at(iteration,state.chain)) == 1);
                                                },
                                                Color::Red => {
                                                    unfold(sized_flip_allowed(SizedFlipChain::LR(p, g, pv, gv, other, uncle, up)));
                                                    unfold(sized_flip_uncle_red(SizedTree::Node(u, ug, uc, uv, ul, ur)));
                                                    have sized_flip_allowed(SizedFlipChain::LR(p, g, pv, gv, other, uncle, up)) == sized_flip_allowed(up) by {
                                                        rewrite(uncle, SizedTree::Node(u, ug, uc, uv, ul, ur)); rewrite(uc, Color::Red);
                                                        unfold(sized_flip_allowed(SizedFlipChain::LR(p, g, pv, gv, other, SizedTree::Node(u, ug, Color::Red, uv, ul, ur), up)));
                                                        unfold(sized_flip_uncle_red(SizedTree::Node(u, ug, Color::Red, uv, ul, ur))); close();
                                                    }
                                                    have sized_flip_allowed(up) == 1 by close();
                                                    let { metadata: u_size, left: u_left, right: u_right } = unfold(uncle_tree);
                                                    have ug == g by {
                                                        if ug == g { close(); } else {
                                                            have sized_parent_is(uncle,g) == 0 by {
                                                                rewrite(uncle, SizedTree::Node(u, ug, uc, uv, ul, ur));
                                                                unfold(sized_parent_is(SizedTree::Node(u, ug, uc, uv, ul, ur),g));
                                                                close() using { not (ug == g); };
                                                            }
                                                            have not (sized_parent_is(uncle,g) == 1) by {
                                                                rewrite(sized_parent_is(uncle,g), 0); close();
                                                            }
                                                            contradiction(sized_parent_is(uncle,g) == 1);
                                                        }
                                                    }
                                                    have separate(memory(p->__rb_parent_color), memory(u->__rb_parent_color)) by close();
                                                    have p != u by close();
                                                    unfold(color_bit(Color::Red)); unfold(color_bit(Color::Black));
                                                    have (u->__rb_parent_color & 1) == 0 by {
                                                        rewrite((u->__rb_parent_color & 1), color_bit(uc));
                                                        rewrite(uc, Color::Red);
                                                        unfold(color_bit(Color::Red)); close();
                                                    }
                                                    have p->__rb_parent_color == address(g) by {
                                                        rewrite(p->__rb_parent_color, address(g) + (p->__rb_parent_color & 1));
                                                        rewrite((p->__rb_parent_color & 1), color_bit(Color::Red));
                                                        rewrite(color_bit(Color::Red), 0); close();
                                                    }
                                                    let links = fold(sized_context_flip_links(root, g, p, u), {
                                                        top: old(root->rb_node), xl: g->rb_left, xr: g->rb_right,
                                                        yl: p->rb_left, yr: p->rb_right, zl: u->rb_left, zr: u->rb_right
                                                    });
                                                    let red_uncle = fold(sized_flip_red_word(u), { word: u->__rb_parent_color });
                                                    unfold(sized_flip_chain_node(sized_flip_parent(up)));
                                                    let grand_word = fold(sized_flip_chain_grand_word(g), {
                                                        up: sized_flip_parent(up), word: g->__rb_parent_color
                                                    });
                                                    have aligned(g, 8) by close();
                                                    step(); step(); step(); step(); step(); step();
                                                    have gparent == g by close();
                                                    have aligned(gparent, 8) by close();
                                                    have (address(gparent) | 1) == address(gparent) + 1 by {
                                                        close() using { aligned(gparent, 8); };
                                                    }
                                                    step(); // Load the grandparent's right child.
                                                    have tmp == u by close();
                                                    have parent != tmp by close();
                                                    step();
                                                    unfold(red_uncle);
                                                    have (u->__rb_parent_color & 1) == 0 by close();
                                                    have (tmp->__rb_parent_color & 1) == 0 by {
                                                        close() using { tmp == u; (u->__rb_parent_color & 1) == 0; };
                                                    }
                                                    step();
                                                    step();
                                                    let uncle_word = fold(sized_context_flip_black_word(tmp, gparent), { word: tmp->__rb_parent_color });
                                                    step();
                                                    let parent_word = fold(sized_context_flip_black_word(parent, gparent), { word: parent->__rb_parent_color });
                                                    step();
                                                    let { kept: grand_word } = step(insert::rb_parent, { word: grand_word });
                                                    step();
                                                    unfold(grand_word);
                                                    have node == g by close();
                                                    have parent == sized_flip_parent(up) by close();
                                                    have aligned(parent, 8) by close();
                                                    step();
                                                    unfold(uncle_word); unfold(parent_word); unfold(links);
                                                    have g->__rb_parent_color == address(parent) by close();
                                                    have (address(parent) & 7u64) == 0u64 by {
                                                        close() using { aligned(parent, 8); };
                                                    }
                                                    have (7u64 & 1u64) == 1u64 by close();
                                                    apply(integer::uint64_mask_subset(address(parent), 7u64, 1u64));
                                                    have (g->__rb_parent_color & 1) == color_bit(Color::Red) by {
                                                        rewrite(g->__rb_parent_color, address(parent));
                                                        rewrite(color_bit(Color::Red), 0); close();
                                                    }
                                                    have g->__rb_parent_color == address(sized_flip_parent(up)) + (g->__rb_parent_color & 1) by {
                                                        rewrite(g->__rb_parent_color, address(parent));
                                                        rewrite(sized_flip_parent(up), parent);
                                                        rewrite((address(parent) & 1u64), 0u64); close();
                                                    }
                                                    have root->rb_node == old(root->rb_node) by close();
                                                    let uncle_tree = fold(sized_at(u), {
                                                        model: SizedTree::Node(u, g, Color::Black, uv, ul, ur), metadata: u_size, left: u_left, right: u_right
                                                    });
                                                    have sized_parent_is(at(iteration,state.model), p) == 1 by {
                                                        rewrite(at(iteration,state.model), SizedTree::Node(current, above, red, count, lo, hi));
                                                        unfold(sized_parent_is(SizedTree::Node(current, above, red, count, lo, hi),p));
                                                        normalize() using { above == p; };
                                                    }
                                                    unfold(sized_value(at(iteration,state.model)));
                                                    have to_integer(pv) == 1 + to_integer(sized_value(other)) + to_integer(sized_value(at(iteration,state.model))) by {
                                                        rewrite(at(iteration,state.model), SizedTree::Node(current, above, red, count, lo, hi));
                                                        unfold(sized_value(SizedTree::Node(current, above, red, count, lo, hi))); close();
                                                    }
                                                    let parent_tree = fold(sized_at(p), { model: SizedTree::Node(p, g, Color::Black, pv, other, at(iteration,state.model)), metadata: p_size, left: other_tree, right: focus });
                                                    unfold(sized_parent_is(SizedTree::Node(p, g, Color::Black, pv, other, at(iteration,state.model)), g));
                                                    unfold(sized_value(SizedTree::Node(p, g, Color::Black, pv, other, at(iteration,state.model))));
                                                    unfold(sized_parent_is(SizedTree::Node(u, g, Color::Black, uv, ul, ur), g));
                                                    unfold(sized_value(SizedTree::Node(u, g, Color::Black, uv, ul, ur)));
                                                    unfold(sized_value(SizedTree::Node(u, ug, uc, uv, ul, ur)));
                                                    have sized_value(uncle) == uv by {
                                                        rewrite(uncle, SizedTree::Node(u, ug, uc, uv, ul, ur));
                                                        unfold(sized_value(SizedTree::Node(u, ug, uc, uv, ul, ur))); normalize();
                                                    }
                                                    let focus = fold(sized_at(g), { model: SizedTree::Node(g, sized_flip_parent(up), Color::Red, gv, SizedTree::Node(p, g, Color::Black, pv, other, at(iteration,state.model)), SizedTree::Node(u, g, Color::Black, uv, ul, ur)), metadata: g_size, left: parent_tree, right: uncle_tree });
                                                    apply(sized_flip_context_parent(up));
                                                    let state = fold(sized_flip_chain_at(root), { root_node: old(root->rb_node), chain: up, model: SizedTree::Node(g, sized_flip_parent(up), Color::Red, gv, SizedTree::Node(p, g, Color::Black, pv, other, at(iteration,state.model)), SizedTree::Node(u, g, Color::Black, uv, ul, ur)), context: sized_flip_context(up), focus: focus, path: outer_path });
                                                    unfold(sized_flip_result(SizedFlipChain::LR(p, g, pv, gv, other, uncle, up), at(iteration,state.model)));
                                                    unfold(sized_recolor(SizedTree::Node(u, ug, uc, uv, ul, ur),Color::Black));
                                                    have sized_flip_result(state.chain,state.model) == sized_flip_result(old(state.chain),old(state.model)) by close();
                                                    apply(sized_flip_depth_nonnegative(up));
                                                    unfold(sized_flip_depth(SizedFlipChain::LR(p, g, pv, gv, other, uncle, up)));
                                                    have sized_flip_depth(state.chain) < sized_flip_depth(at(iteration,state.chain)) by {
                                                        rewrite(state.chain, up);
                                                        rewrite(at(iteration,state.chain), SizedFlipChain::LR(p, g, pv, gv, other, uncle, up));
                                                        unfold(sized_flip_depth(SizedFlipChain::LR(p, g, pv, gv, other, uncle, up))); close() using {};
                                                    }
                                                    unfold(sized_flip_node(SizedTree::Node(g, sized_flip_parent(up), Color::Red, gv, SizedTree::Node(p, g, Color::Black, pv, other, at(iteration,state.model)), SizedTree::Node(u, g, Color::Black, uv, ul, ur))));
                                                    unfold(sized_flip_color(SizedTree::Node(g, sized_flip_parent(up), Color::Red, gv, SizedTree::Node(p, g, Color::Black, pv, other, at(iteration,state.model)), SizedTree::Node(u, g, Color::Black, uv, ul, ur))));
                                                    step();
                                                },
                                            }
                                        },
                                    }
                                },
                                SizedFlipChain::RL(p, g, pv, gv, other, uncle, up) => {
                                    have path.model == SizedContext::Left(p, g, Color::Red, pv, other, SizedContext::Right(g, sized_flip_parent(up), Color::Black, gv, uncle, sized_flip_context(up))) by {
                                        rewrite(path.model, at(iteration,state.context));
                                        rewrite(at(iteration,state.context), sized_flip_context(at(iteration,state.chain)));
                                        rewrite(at(iteration,state.chain), SizedFlipChain::RL(p, g, pv, gv, other, uncle, up));
                                        unfold(sized_flip_context(SizedFlipChain::RL(p, g, pv, gv, other, uncle, up))); normalize();
                                    }
                                    let { metadata: p_size, sibling: other_tree, up: g_path } = unfold(path);
                                    let { metadata: g_size, sibling: uncle_tree, up: outer_path } = unfold(g_path);
                                    have parent == p by {
                                        rewrite(parent, sized_flip_parent(at(iteration,state.chain)));
                                        rewrite(at(iteration,state.chain), SizedFlipChain::RL(p, g, pv, gv, other, uncle, up));
                                        unfold(sized_flip_parent(SizedFlipChain::RL(p, g, pv, gv, other, uncle, up))); normalize();
                                    }
                                    match uncle {
                                        SizedTree::Empty => {
                                            unfold(sized_flip_allowed(SizedFlipChain::RL(p, g, pv, gv, other, uncle, up)));
                                            unfold(sized_flip_uncle_red(SizedTree::Empty));
                                            have sized_flip_allowed(SizedFlipChain::RL(p, g, pv, gv, other, uncle, up)) == 0 by { rewrite(uncle, SizedTree::Empty); unfold(sized_flip_allowed(SizedFlipChain::RL(p, g, pv, gv, other, SizedTree::Empty, up))); unfold(sized_flip_uncle_red(SizedTree::Empty)); normalize(); }
                                            have not (sized_flip_allowed(at(iteration,state.chain)) == 1) by {
                                                rewrite(at(iteration,state.chain), SizedFlipChain::RL(p, g, pv, gv, other, uncle, up));
                                                rewrite(sized_flip_allowed(SizedFlipChain::RL(p, g, pv, gv, other, uncle, up)), 0); normalize();
                                            }
                                            contradiction(sized_flip_allowed(at(iteration,state.chain)) == 1);
                                        },
                                        SizedTree::Node(u, ug, uc, uv, ul, ur) => {
                                            match uc {
                                                Color::Black => {
                                                    unfold(sized_flip_allowed(SizedFlipChain::RL(p, g, pv, gv, other, uncle, up)));
                                                    unfold(sized_flip_uncle_red(SizedTree::Node(u, ug, uc, uv, ul, ur)));
                                                    have sized_flip_allowed(SizedFlipChain::RL(p, g, pv, gv, other, uncle, up)) == 0 by { rewrite(uncle, SizedTree::Node(u, ug, uc, uv, ul, ur)); rewrite(uc, Color::Black); unfold(sized_flip_allowed(SizedFlipChain::RL(p, g, pv, gv, other, SizedTree::Node(u, ug, Color::Black, uv, ul, ur), up))); unfold(sized_flip_uncle_red(SizedTree::Node(u, ug, Color::Black, uv, ul, ur))); normalize(); }
                                                    have not (sized_flip_allowed(at(iteration,state.chain)) == 1) by {
                                                        rewrite(at(iteration,state.chain), SizedFlipChain::RL(p, g, pv, gv, other, uncle, up));
                                                        rewrite(sized_flip_allowed(SizedFlipChain::RL(p, g, pv, gv, other, uncle, up)), 0); normalize();
                                                    }
                                                    contradiction(sized_flip_allowed(at(iteration,state.chain)) == 1);
                                                },
                                                Color::Red => {
                                                    unfold(sized_flip_allowed(SizedFlipChain::RL(p, g, pv, gv, other, uncle, up)));
                                                    unfold(sized_flip_uncle_red(SizedTree::Node(u, ug, uc, uv, ul, ur)));
                                                    have sized_flip_allowed(SizedFlipChain::RL(p, g, pv, gv, other, uncle, up)) == sized_flip_allowed(up) by {
                                                        rewrite(uncle, SizedTree::Node(u, ug, uc, uv, ul, ur)); rewrite(uc, Color::Red);
                                                        unfold(sized_flip_allowed(SizedFlipChain::RL(p, g, pv, gv, other, SizedTree::Node(u, ug, Color::Red, uv, ul, ur), up)));
                                                        unfold(sized_flip_uncle_red(SizedTree::Node(u, ug, Color::Red, uv, ul, ur))); normalize();
                                                    }
                                                    have sized_flip_allowed(up) == 1 by close();
                                                    let { metadata: u_size, left: u_left, right: u_right } = unfold(uncle_tree);
                                                    have ug == g by {
                                                        if ug == g { close(); } else {
                                                            have sized_parent_is(uncle,g) == 0 by {
                                                                rewrite(uncle, SizedTree::Node(u, ug, uc, uv, ul, ur));
                                                                unfold(sized_parent_is(SizedTree::Node(u, ug, uc, uv, ul, ur),g));
                                                                normalize() using { not (ug == g); };
                                                            }
                                                            have not (sized_parent_is(uncle,g) == 1) by {
                                                                rewrite(sized_parent_is(uncle,g), 0); normalize();
                                                            }
                                                            contradiction(sized_parent_is(uncle,g) == 1);
                                                        }
                                                    }
                                                    have separate(memory(p->__rb_parent_color), memory(u->__rb_parent_color)) by close();
                                                    have p != u by close();
                                                    unfold(color_bit(Color::Red)); unfold(color_bit(Color::Black));
                                                    have (u->__rb_parent_color & 1) == 0 by {
                                                        rewrite((u->__rb_parent_color & 1), color_bit(uc));
                                                        rewrite(uc, Color::Red);
                                                        unfold(color_bit(Color::Red)); normalize();
                                                    }
                                                    have p->__rb_parent_color == address(g) by {
                                                        rewrite(p->__rb_parent_color, address(g) + (p->__rb_parent_color & 1));
                                                        rewrite((p->__rb_parent_color & 1), color_bit(Color::Red));
                                                        rewrite(color_bit(Color::Red), 0); normalize();
                                                    }
                                                    let links = fold(sized_context_flip_links(root, g, p, u), {
                                                        top: old(root->rb_node), xl: g->rb_left, xr: g->rb_right,
                                                        yl: p->rb_left, yr: p->rb_right, zl: u->rb_left, zr: u->rb_right
                                                    });
                                                    let red_uncle = fold(sized_flip_red_word(u), { word: u->__rb_parent_color });
                                                    unfold(sized_flip_chain_node(sized_flip_parent(up)));
                                                    let grand_word = fold(sized_flip_chain_grand_word(g), {
                                                        up: sized_flip_parent(up), word: g->__rb_parent_color
                                                    });
                                                    have aligned(g, 8) by close();
                                                    step(); step(); step(); step(); step(); step();
                                                    have gparent == g by close();
                                                    have aligned(gparent, 8) by close();
                                                    have (address(gparent) | 1) == address(gparent) + 1 by {
                                                        normalize() using { aligned(gparent, 8); };
                                                    }
                                                    step(); // Load the grandparent's right child.
                                                    have parent == tmp by close();
                                                    step();
                                                    step();
                                                    have tmp == u by close();
                                                    unfold(red_uncle);
                                                    have (u->__rb_parent_color & 1) == 0 by close();
                                                    have (tmp->__rb_parent_color & 1) == 0 by {
                                                        normalize() using { tmp == u; (u->__rb_parent_color & 1) == 0; };
                                                    }
                                                    step();
                                                    step();
                                                    let uncle_word = fold(sized_context_flip_black_word(tmp, gparent), { word: tmp->__rb_parent_color });
                                                    step();
                                                    let parent_word = fold(sized_context_flip_black_word(parent, gparent), { word: parent->__rb_parent_color });
                                                    step();
                                                    let { kept: grand_word } = step(insert::rb_parent, { word: grand_word });
                                                    step();
                                                    unfold(grand_word);
                                                    have node == g by close();
                                                    have parent == sized_flip_parent(up) by close();
                                                    have aligned(parent, 8) by close();
                                                    step();
                                                    unfold(uncle_word); unfold(parent_word); unfold(links);
                                                    have g->__rb_parent_color == address(parent) by close();
                                                    have (address(parent) & 7u64) == 0u64 by {
                                                        close() using { aligned(parent, 8); };
                                                    }
                                                    have (7u64 & 1u64) == 1u64 by normalize();
                                                    apply(integer::uint64_mask_subset(address(parent), 7u64, 1u64));
                                                    have (g->__rb_parent_color & 1) == color_bit(Color::Red) by {
                                                        rewrite(g->__rb_parent_color, address(parent));
                                                        rewrite(color_bit(Color::Red), 0); close();
                                                    }
                                                    have g->__rb_parent_color == address(sized_flip_parent(up)) + (g->__rb_parent_color & 1) by {
                                                        rewrite(g->__rb_parent_color, address(parent));
                                                        rewrite(sized_flip_parent(up), parent);
                                                        rewrite((address(parent) & 1u64), 0u64); normalize();
                                                    }
                                                    have root->rb_node == old(root->rb_node) by close();
                                                    let uncle_tree = fold(sized_at(u), {
                                                        model: SizedTree::Node(u, g, Color::Black, uv, ul, ur), metadata: u_size, left: u_left, right: u_right
                                                    });
                                                    have sized_parent_is(at(iteration,state.model), p) == 1 by {
                                                        rewrite(at(iteration,state.model), SizedTree::Node(current, above, red, count, lo, hi));
                                                        unfold(sized_parent_is(SizedTree::Node(current, above, red, count, lo, hi),p));
                                                        normalize() using { above == p; };
                                                    }
                                                    unfold(sized_value(at(iteration,state.model)));
                                                    have to_integer(pv) == 1 + to_integer(sized_value(at(iteration,state.model))) + to_integer(sized_value(other)) by {
                                                        rewrite(at(iteration,state.model), SizedTree::Node(current, above, red, count, lo, hi));
                                                        unfold(sized_value(SizedTree::Node(current, above, red, count, lo, hi))); close();
                                                    }
                                                    let parent_tree = fold(sized_at(p), { model: SizedTree::Node(p, g, Color::Black, pv, at(iteration,state.model), other), metadata: p_size, left: focus, right: other_tree });
                                                    unfold(sized_parent_is(SizedTree::Node(p, g, Color::Black, pv, at(iteration,state.model), other), g));
                                                    unfold(sized_value(SizedTree::Node(p, g, Color::Black, pv, at(iteration,state.model), other)));
                                                    unfold(sized_parent_is(SizedTree::Node(u, g, Color::Black, uv, ul, ur), g));
                                                    unfold(sized_value(SizedTree::Node(u, g, Color::Black, uv, ul, ur)));
                                                    unfold(sized_value(SizedTree::Node(u, ug, uc, uv, ul, ur)));
                                                    have sized_value(uncle) == uv by {
                                                        rewrite(uncle, SizedTree::Node(u, ug, uc, uv, ul, ur));
                                                        unfold(sized_value(SizedTree::Node(u, ug, uc, uv, ul, ur))); normalize();
                                                    }
                                                    let focus = fold(sized_at(g), { model: SizedTree::Node(g, sized_flip_parent(up), Color::Red, gv, SizedTree::Node(u, g, Color::Black, uv, ul, ur), SizedTree::Node(p, g, Color::Black, pv, at(iteration,state.model), other)), metadata: g_size, left: uncle_tree, right: parent_tree });
                                                    apply(sized_flip_context_parent(up));
                                                    let state = fold(sized_flip_chain_at(root), { root_node: old(root->rb_node), chain: up, model: SizedTree::Node(g, sized_flip_parent(up), Color::Red, gv, SizedTree::Node(u, g, Color::Black, uv, ul, ur), SizedTree::Node(p, g, Color::Black, pv, at(iteration,state.model), other)), context: sized_flip_context(up), focus: focus, path: outer_path });
                                                    unfold(sized_flip_result(SizedFlipChain::RL(p, g, pv, gv, other, uncle, up), at(iteration,state.model)));
                                                    unfold(sized_recolor(SizedTree::Node(u, ug, uc, uv, ul, ur),Color::Black));
                                                    have sized_flip_result(state.chain,state.model) == sized_flip_result(old(state.chain),old(state.model)) by close();
                                                    apply(sized_flip_depth_nonnegative(up));
                                                    unfold(sized_flip_depth(SizedFlipChain::RL(p, g, pv, gv, other, uncle, up)));
                                                    have sized_flip_depth(state.chain) < sized_flip_depth(at(iteration,state.chain)) by {
                                                        rewrite(state.chain, up);
                                                        rewrite(at(iteration,state.chain), SizedFlipChain::RL(p, g, pv, gv, other, uncle, up));
                                                        unfold(sized_flip_depth(SizedFlipChain::RL(p, g, pv, gv, other, uncle, up))); close() using {};
                                                    }
                                                    unfold(sized_flip_node(SizedTree::Node(g, sized_flip_parent(up), Color::Red, gv, SizedTree::Node(u, g, Color::Black, uv, ul, ur), SizedTree::Node(p, g, Color::Black, pv, at(iteration,state.model), other))));
                                                    unfold(sized_flip_color(SizedTree::Node(g, sized_flip_parent(up), Color::Red, gv, SizedTree::Node(u, g, Color::Black, uv, ul, ur), SizedTree::Node(p, g, Color::Black, pv, at(iteration,state.model), other))));
                                                    step();
                                                },
                                            }
                                        },
                                    }
                                },
                                SizedFlipChain::RR(p, g, pv, gv, other, uncle, up) => {
                                    have path.model == SizedContext::Right(p, g, Color::Red, pv, other, SizedContext::Right(g, sized_flip_parent(up), Color::Black, gv, uncle, sized_flip_context(up))) by {
                                        rewrite(path.model, at(iteration,state.context));
                                        rewrite(at(iteration,state.context), sized_flip_context(at(iteration,state.chain)));
                                        rewrite(at(iteration,state.chain), SizedFlipChain::RR(p, g, pv, gv, other, uncle, up));
                                        unfold(sized_flip_context(SizedFlipChain::RR(p, g, pv, gv, other, uncle, up))); normalize();
                                    }
                                    let { metadata: p_size, sibling: other_tree, up: g_path } = unfold(path);
                                    let { metadata: g_size, sibling: uncle_tree, up: outer_path } = unfold(g_path);
                                    have parent == p by {
                                        rewrite(parent, sized_flip_parent(at(iteration,state.chain)));
                                        rewrite(at(iteration,state.chain), SizedFlipChain::RR(p, g, pv, gv, other, uncle, up));
                                        unfold(sized_flip_parent(SizedFlipChain::RR(p, g, pv, gv, other, uncle, up))); normalize();
                                    }
                                    match uncle {
                                        SizedTree::Empty => {
                                            unfold(sized_flip_allowed(SizedFlipChain::RR(p, g, pv, gv, other, uncle, up)));
                                            unfold(sized_flip_uncle_red(SizedTree::Empty));
                                            have sized_flip_allowed(SizedFlipChain::RR(p, g, pv, gv, other, uncle, up)) == 0 by { rewrite(uncle, SizedTree::Empty); unfold(sized_flip_allowed(SizedFlipChain::RR(p, g, pv, gv, other, SizedTree::Empty, up))); unfold(sized_flip_uncle_red(SizedTree::Empty)); normalize(); }
                                            have not (sized_flip_allowed(at(iteration,state.chain)) == 1) by {
                                                rewrite(at(iteration,state.chain), SizedFlipChain::RR(p, g, pv, gv, other, uncle, up));
                                                rewrite(sized_flip_allowed(SizedFlipChain::RR(p, g, pv, gv, other, uncle, up)), 0); normalize();
                                            }
                                            contradiction(sized_flip_allowed(at(iteration,state.chain)) == 1);
                                        },
                                        SizedTree::Node(u, ug, uc, uv, ul, ur) => {
                                            match uc {
                                                Color::Black => {
                                                    unfold(sized_flip_allowed(SizedFlipChain::RR(p, g, pv, gv, other, uncle, up)));
                                                    unfold(sized_flip_uncle_red(SizedTree::Node(u, ug, uc, uv, ul, ur)));
                                                    have sized_flip_allowed(SizedFlipChain::RR(p, g, pv, gv, other, uncle, up)) == 0 by { rewrite(uncle, SizedTree::Node(u, ug, uc, uv, ul, ur)); rewrite(uc, Color::Black); unfold(sized_flip_allowed(SizedFlipChain::RR(p, g, pv, gv, other, SizedTree::Node(u, ug, Color::Black, uv, ul, ur), up))); unfold(sized_flip_uncle_red(SizedTree::Node(u, ug, Color::Black, uv, ul, ur))); normalize(); }
                                                    have not (sized_flip_allowed(at(iteration,state.chain)) == 1) by {
                                                        rewrite(at(iteration,state.chain), SizedFlipChain::RR(p, g, pv, gv, other, uncle, up));
                                                        rewrite(sized_flip_allowed(SizedFlipChain::RR(p, g, pv, gv, other, uncle, up)), 0); normalize();
                                                    }
                                                    contradiction(sized_flip_allowed(at(iteration,state.chain)) == 1);
                                                },
                                                Color::Red => {
                                                    unfold(sized_flip_allowed(SizedFlipChain::RR(p, g, pv, gv, other, uncle, up)));
                                                    unfold(sized_flip_uncle_red(SizedTree::Node(u, ug, uc, uv, ul, ur)));
                                                    have sized_flip_allowed(SizedFlipChain::RR(p, g, pv, gv, other, uncle, up)) == sized_flip_allowed(up) by {
                                                        rewrite(uncle, SizedTree::Node(u, ug, uc, uv, ul, ur)); rewrite(uc, Color::Red);
                                                        unfold(sized_flip_allowed(SizedFlipChain::RR(p, g, pv, gv, other, SizedTree::Node(u, ug, Color::Red, uv, ul, ur), up)));
                                                        unfold(sized_flip_uncle_red(SizedTree::Node(u, ug, Color::Red, uv, ul, ur))); normalize();
                                                    }
                                                    have sized_flip_allowed(up) == 1 by close();
                                                    let { metadata: u_size, left: u_left, right: u_right } = unfold(uncle_tree);
                                                    have ug == g by {
                                                        if ug == g { close(); } else {
                                                            have sized_parent_is(uncle,g) == 0 by {
                                                                rewrite(uncle, SizedTree::Node(u, ug, uc, uv, ul, ur));
                                                                unfold(sized_parent_is(SizedTree::Node(u, ug, uc, uv, ul, ur),g));
                                                                normalize() using { not (ug == g); };
                                                            }
                                                            have not (sized_parent_is(uncle,g) == 1) by {
                                                                rewrite(sized_parent_is(uncle,g), 0); normalize();
                                                            }
                                                            contradiction(sized_parent_is(uncle,g) == 1);
                                                        }
                                                    }
                                                    have separate(memory(p->__rb_parent_color), memory(u->__rb_parent_color)) by close();
                                                    have p != u by close();
                                                    unfold(color_bit(Color::Red)); unfold(color_bit(Color::Black));
                                                    have (u->__rb_parent_color & 1) == 0 by {
                                                        rewrite((u->__rb_parent_color & 1), color_bit(uc));
                                                        rewrite(uc, Color::Red);
                                                        unfold(color_bit(Color::Red)); normalize();
                                                    }
                                                    have p->__rb_parent_color == address(g) by {
                                                        rewrite(p->__rb_parent_color, address(g) + (p->__rb_parent_color & 1));
                                                        rewrite((p->__rb_parent_color & 1), color_bit(Color::Red));
                                                        rewrite(color_bit(Color::Red), 0); normalize();
                                                    }
                                                    let links = fold(sized_context_flip_links(root, g, p, u), {
                                                        top: old(root->rb_node), xl: g->rb_left, xr: g->rb_right,
                                                        yl: p->rb_left, yr: p->rb_right, zl: u->rb_left, zr: u->rb_right
                                                    });
                                                    let red_uncle = fold(sized_flip_red_word(u), { word: u->__rb_parent_color });
                                                    unfold(sized_flip_chain_node(sized_flip_parent(up)));
                                                    let grand_word = fold(sized_flip_chain_grand_word(g), {
                                                        up: sized_flip_parent(up), word: g->__rb_parent_color
                                                    });
                                                    have aligned(g, 8) by close();
                                                    step(); step(); step(); step(); step(); step();
                                                    have gparent == g by close();
                                                    have aligned(gparent, 8) by close();
                                                    have (address(gparent) | 1) == address(gparent) + 1 by {
                                                        normalize() using { aligned(gparent, 8); };
                                                    }
                                                    step(); // Load the grandparent's right child.
                                                    have parent == tmp by close();
                                                    step();
                                                    step();
                                                    have tmp == u by close();
                                                    unfold(red_uncle);
                                                    have (u->__rb_parent_color & 1) == 0 by close();
                                                    have (tmp->__rb_parent_color & 1) == 0 by {
                                                        normalize() using { tmp == u; (u->__rb_parent_color & 1) == 0; };
                                                    }
                                                    step();
                                                    step();
                                                    let uncle_word = fold(sized_context_flip_black_word(tmp, gparent), { word: tmp->__rb_parent_color });
                                                    step();
                                                    let parent_word = fold(sized_context_flip_black_word(parent, gparent), { word: parent->__rb_parent_color });
                                                    step();
                                                    let { kept: grand_word } = step(insert::rb_parent, { word: grand_word });
                                                    step();
                                                    unfold(grand_word);
                                                    have node == g by close();
                                                    have parent == sized_flip_parent(up) by close();
                                                    have aligned(parent, 8) by close();
                                                    step();
                                                    unfold(uncle_word); unfold(parent_word); unfold(links);
                                                    have g->__rb_parent_color == address(parent) by close();
                                                    have (address(parent) & 7u64) == 0u64 by {
                                                        close() using { aligned(parent, 8); };
                                                    }
                                                    have (7u64 & 1u64) == 1u64 by normalize();
                                                    apply(integer::uint64_mask_subset(address(parent), 7u64, 1u64));
                                                    have (g->__rb_parent_color & 1) == color_bit(Color::Red) by {
                                                        rewrite(g->__rb_parent_color, address(parent));
                                                        rewrite(color_bit(Color::Red), 0); close();
                                                    }
                                                    have g->__rb_parent_color == address(sized_flip_parent(up)) + (g->__rb_parent_color & 1) by {
                                                        rewrite(g->__rb_parent_color, address(parent));
                                                        rewrite(sized_flip_parent(up), parent);
                                                        rewrite((address(parent) & 1u64), 0u64); normalize();
                                                    }
                                                    have root->rb_node == old(root->rb_node) by close();
                                                    let uncle_tree = fold(sized_at(u), {
                                                        model: SizedTree::Node(u, g, Color::Black, uv, ul, ur), metadata: u_size, left: u_left, right: u_right
                                                    });
                                                    have sized_parent_is(at(iteration,state.model), p) == 1 by {
                                                        rewrite(at(iteration,state.model), SizedTree::Node(current, above, red, count, lo, hi));
                                                        unfold(sized_parent_is(SizedTree::Node(current, above, red, count, lo, hi),p));
                                                        normalize() using { above == p; };
                                                    }
                                                    unfold(sized_value(at(iteration,state.model)));
                                                    have to_integer(pv) == 1 + to_integer(sized_value(other)) + to_integer(sized_value(at(iteration,state.model))) by {
                                                        rewrite(at(iteration,state.model), SizedTree::Node(current, above, red, count, lo, hi));
                                                        unfold(sized_value(SizedTree::Node(current, above, red, count, lo, hi))); close();
                                                    }
                                                    let parent_tree = fold(sized_at(p), { model: SizedTree::Node(p, g, Color::Black, pv, other, at(iteration,state.model)), metadata: p_size, left: other_tree, right: focus });
                                                    unfold(sized_parent_is(SizedTree::Node(p, g, Color::Black, pv, other, at(iteration,state.model)), g));
                                                    unfold(sized_value(SizedTree::Node(p, g, Color::Black, pv, other, at(iteration,state.model))));
                                                    unfold(sized_parent_is(SizedTree::Node(u, g, Color::Black, uv, ul, ur), g));
                                                    unfold(sized_value(SizedTree::Node(u, g, Color::Black, uv, ul, ur)));
                                                    unfold(sized_value(SizedTree::Node(u, ug, uc, uv, ul, ur)));
                                                    have sized_value(uncle) == uv by {
                                                        rewrite(uncle, SizedTree::Node(u, ug, uc, uv, ul, ur));
                                                        unfold(sized_value(SizedTree::Node(u, ug, uc, uv, ul, ur))); normalize();
                                                    }
                                                    let focus = fold(sized_at(g), { model: SizedTree::Node(g, sized_flip_parent(up), Color::Red, gv, SizedTree::Node(u, g, Color::Black, uv, ul, ur), SizedTree::Node(p, g, Color::Black, pv, other, at(iteration,state.model))), metadata: g_size, left: uncle_tree, right: parent_tree });
                                                    apply(sized_flip_context_parent(up));
                                                    let state = fold(sized_flip_chain_at(root), { root_node: old(root->rb_node), chain: up, model: SizedTree::Node(g, sized_flip_parent(up), Color::Red, gv, SizedTree::Node(u, g, Color::Black, uv, ul, ur), SizedTree::Node(p, g, Color::Black, pv, other, at(iteration,state.model))), context: sized_flip_context(up), focus: focus, path: outer_path });
                                                    unfold(sized_flip_result(SizedFlipChain::RR(p, g, pv, gv, other, uncle, up), at(iteration,state.model)));
                                                    unfold(sized_recolor(SizedTree::Node(u, ug, uc, uv, ul, ur),Color::Black));
                                                    have sized_flip_result(state.chain,state.model) == sized_flip_result(old(state.chain),old(state.model)) by close();
                                                    apply(sized_flip_depth_nonnegative(up));
                                                    unfold(sized_flip_depth(SizedFlipChain::RR(p, g, pv, gv, other, uncle, up)));
                                                    have sized_flip_depth(state.chain) < sized_flip_depth(at(iteration,state.chain)) by {
                                                        rewrite(state.chain, up);
                                                        rewrite(at(iteration,state.chain), SizedFlipChain::RR(p, g, pv, gv, other, uncle, up));
                                                        unfold(sized_flip_depth(SizedFlipChain::RR(p, g, pv, gv, other, uncle, up))); close() using {};
                                                    }
                                                    unfold(sized_flip_node(SizedTree::Node(g, sized_flip_parent(up), Color::Red, gv, SizedTree::Node(u, g, Color::Black, uv, ul, ur), SizedTree::Node(p, g, Color::Black, pv, other, at(iteration,state.model)))));
                                                    unfold(sized_flip_color(SizedTree::Node(g, sized_flip_parent(up), Color::Red, gv, SizedTree::Node(u, g, Color::Black, uv, ul, ur), SizedTree::Node(p, g, Color::Black, pv, other, at(iteration,state.model)))));
                                                    step();
                                                },
                                            }
                                        },
                                    }
                                },
                                SizedFlipChain::Root => {
                                    have path.model == SizedContext::Top by {
                                        rewrite(path.model, at(iteration,state.context));
                                        rewrite(at(iteration,state.context), sized_flip_context(at(iteration,state.chain)));
                                        rewrite(at(iteration,state.chain), SizedFlipChain::Root);
                                        unfold(sized_flip_context(SizedFlipChain::Root)); normalize();
                                    }
                                    have parent == 0 by {
                                        rewrite(parent, above);
                                        rewrite(above, sized_context_parent(at(iteration,state.context), 0));
                                        rewrite(at(iteration,state.context), sized_flip_context(at(iteration,state.chain)));
                                        rewrite(at(iteration,state.chain), SizedFlipChain::Root);
                                        unfold(sized_flip_context(SizedFlipChain::Root));
                                        unfold(sized_context_parent(SizedContext::Top, 0)); normalize();
                                    }
                                    let { metadata: metadata, left: l, right: r } = unfold(focus);
                                    let branch_link = fold(sized_flip_chain_root_link(root), { node: old(root->rb_node) });
                                    step(); step();
                                    unfold(branch_link);
                                    have root->rb_node == old(root->rb_node) by close();
                                    have current->__rb_parent_color == 1 by close();
                                    have node->__rb_parent_color == 1 by { rewrite(node, current); close(); }
                                    unfold(color_bit(Color::Black));
                                    have (node->__rb_parent_color & 1) == color_bit(Color::Black) by {
                                        rewrite(node->__rb_parent_color, 1);
                                        rewrite(color_bit(Color::Black), 1); normalize();
                                    }
                                    let focus = fold(sized_at(node), { model: SizedTree::Node(current, 0, Color::Black, count, lo, hi), metadata: metadata, left: l, right: r });
                                    have sized_value(focus.model) == count by {
                                        rewrite(focus.model, SizedTree::Node(current, 0, Color::Black, count, lo, hi));
                                        unfold(sized_value(SizedTree::Node(current, 0, Color::Black, count, lo, hi))); normalize();
                                    }
                                    have sized_parent_is(focus.model, sized_context_parent(path.model, 0)) == 1 by {
                                        rewrite(focus.model, SizedTree::Node(current, 0, Color::Black, count, lo, hi));
                                        rewrite(path.model, SizedContext::Top);
                                        unfold(sized_context_parent(SizedContext::Top, 0));
                                        unfold(sized_parent_is(SizedTree::Node(current, 0, Color::Black, count, lo, hi), 0)); normalize();
                                    }
                                    have sized_plug(path.model, focus.model) == sized_flip_result(at(iteration,state.chain), at(iteration,state.model)) by {
                                        rewrite(path.model, SizedContext::Top);
                                        rewrite(focus.model, SizedTree::Node(current, 0, Color::Black, count, lo, hi));
                                        rewrite(at(iteration,state.chain), SizedFlipChain::Root);
                                        rewrite(at(iteration,state.model), SizedTree::Node(current, above, red, count, lo, hi));
                                        unfold(sized_flip_result(SizedFlipChain::Root, SizedTree::Node(current, above, red, count, lo, hi)));
                                        unfold(sized_recolor(SizedTree::Node(current, above, red, count, lo, hi), Color::Black));
                                        unfold(sized_plug(SizedContext::Top, SizedTree::Node(current, 0, Color::Black, count, lo, hi)));
                                        have above == 0 by close();
                                        rewrite(above, 0); normalize();
                                    }
                                    have 0 == sized_context_parent(SizedContext::Top, 0) by {
                                        unfold(sized_context_parent(SizedContext::Top, 0)); normalize();
                                    }
                                    let state = fold(sized_flip_chain_at(root), { root_node: old(root->rb_node), chain: at(iteration,state.chain), model: SizedTree::Node(current, 0, Color::Black, count, lo, hi), context: SizedContext::Top, focus: focus, path: path });
                                    have sized_plug(state.context, state.model) == sized_flip_result(at(iteration,state.chain), at(iteration,state.model)) by close();
                                    have sized_plug(state.context, state.model) == sized_flip_result(old(state.chain), old(state.model)) by close();
                                    step();
                                },
                                SizedFlipChain::Stop(ctx) => {
                                    have path.model == ctx by {
                                        rewrite(path.model, at(iteration,state.context));
                                        rewrite(at(iteration,state.context), sized_flip_context(at(iteration,state.chain)));
                                        rewrite(at(iteration,state.chain), SizedFlipChain::Stop(ctx));
                                        unfold(sized_flip_context(SizedFlipChain::Stop(ctx))); normalize();
                                    }
                                    have sized_flip_black_boundary(ctx) == 1 by {
                                        unfold(sized_flip_allowed(SizedFlipChain::Stop(ctx)));
                                        rewrite(sized_flip_black_boundary(ctx), sized_flip_allowed(SizedFlipChain::Stop(ctx)));
                                        rewrite(SizedFlipChain::Stop(ctx), at(iteration,state.chain)); close();
                                    }
                                    match ctx {
                                        SizedContext::Top => {
                                            have not (sized_flip_black_boundary(ctx) == 1) by {
                                                rewrite(ctx, SizedContext::Top);
                                                unfold(sized_flip_black_boundary(SizedContext::Top)); normalize();
                                            }
                                            contradiction(sized_flip_black_boundary(ctx) == 1);
                                        },
                                        SizedContext::Left(a, gp, color, cached, sibling, up) => {
                                            have parent == a by {
                                                rewrite(parent, above);
                                                rewrite(above, sized_context_parent(at(iteration,state.context), 0));
                                                rewrite(at(iteration,state.context), path.model);
                                                rewrite(path.model, ctx); rewrite(ctx, SizedContext::Left(a, gp, color, cached, sibling, up));
                                                unfold(sized_context_parent(SizedContext::Left(a, gp, color, cached, sibling, up), 0)); normalize();
                                            }
                                            have color_bit(color) == 1 by {
                                                unfold(sized_flip_black_boundary(SizedContext::Left(a, gp, color, cached, sibling, up)));
                                                rewrite(color_bit(color), sized_flip_black_boundary(SizedContext::Left(a, gp, color, cached, sibling, up)));
                                                rewrite(SizedContext::Left(a, gp, color, cached, sibling, up), ctx); close();
                                            }
                                            let { metadata: a_size, sibling: held_sibling, up: held_up } = unfold(path);
                                            have (a->__rb_parent_color & 1) == 1 by {
                                                rewrite((a->__rb_parent_color & 1), color_bit(color));
                                                rewrite(color_bit(color), 1); normalize();
                                            }
                                            let path = fold(sized_context_at(node, root->rb_node, 0, count), { model: SizedContext::Left(a, gp, color, cached, sibling, up), metadata: a_size, sibling: held_sibling, up: held_up });
                                            let branch_link = fold(sized_flip_chain_root_link(root), { node: old(root->rb_node) });
                                            step(); step(); step();
                                            unfold(branch_link);
                                            have root->rb_node == old(root->rb_node) by close();
                                            have sized_value(focus.model) == count by {
                                                rewrite(focus.model, at(iteration,state.model));
                                                rewrite(at(iteration,state.model), SizedTree::Node(current, above, red, count, lo, hi));
                                                unfold(sized_value(SizedTree::Node(current, above, red, count, lo, hi))); normalize();
                                            }
                                            have sized_parent_is(focus.model, sized_context_parent(path.model, 0)) == 1 by {
                                                rewrite(focus.model, at(iteration,state.model));
                                                rewrite(at(iteration,state.model), SizedTree::Node(current, above, red, count, lo, hi));
                                                unfold(sized_parent_is(SizedTree::Node(current, above, red, count, lo, hi), sized_context_parent(path.model, 0)));
                                                normalize() using { above == sized_context_parent(at(iteration,state.context), 0); at(iteration,state.context) == ctx; ctx == SizedContext::Left(a, gp, color, cached, sibling, up); path.model == SizedContext::Left(a, gp, color, cached, sibling, up); };
                                            }
                                            have sized_plug(path.model, focus.model) == sized_flip_result(at(iteration,state.chain), at(iteration,state.model)) by {
                                                rewrite(at(iteration,state.chain), SizedFlipChain::Stop(ctx));
                                                unfold(sized_flip_result(SizedFlipChain::Stop(ctx), at(iteration,state.model)));
                                                rewrite(focus.model, at(iteration,state.model));
                                                rewrite(path.model, SizedContext::Left(a, gp, color, cached, sibling, up)); rewrite(SizedContext::Left(a, gp, color, cached, sibling, up), ctx); normalize();
                                            }
                                            have above == sized_context_parent(SizedContext::Left(a, gp, color, cached, sibling, up), 0) by {
                                                rewrite(above, parent);
                                                unfold(sized_context_parent(SizedContext::Left(a, gp, color, cached, sibling, up), 0)); close();
                                            }
                                            let state = fold(sized_flip_chain_at(root), {
                                                root_node: old(root->rb_node),
                                                chain: at(iteration,state.chain),
                                                model: SizedTree::Node(current, above, red, count, lo, hi),
                                                context: SizedContext::Left(a, gp, color, cached, sibling, up),
                                                focus: focus, path: path
                                            });
                                            have sized_plug(state.context, state.model) == sized_flip_result(at(iteration,state.chain), at(iteration,state.model)) by close();
                                            have sized_plug(state.context, state.model) == sized_flip_result(old(state.chain), old(state.model)) by close();
                                            step();
                                        },
                                        SizedContext::Right(a, gp, color, cached, sibling, up) => {
                                            have parent == a by {
                                                rewrite(parent, above);
                                                rewrite(above, sized_context_parent(at(iteration,state.context), 0));
                                                rewrite(at(iteration,state.context), path.model);
                                                rewrite(path.model, ctx); rewrite(ctx, SizedContext::Right(a, gp, color, cached, sibling, up));
                                                unfold(sized_context_parent(SizedContext::Right(a, gp, color, cached, sibling, up), 0)); normalize();
                                            }
                                            have color_bit(color) == 1 by {
                                                unfold(sized_flip_black_boundary(SizedContext::Right(a, gp, color, cached, sibling, up)));
                                                rewrite(color_bit(color), sized_flip_black_boundary(SizedContext::Right(a, gp, color, cached, sibling, up)));
                                                rewrite(SizedContext::Right(a, gp, color, cached, sibling, up), ctx); close();
                                            }
                                            let { metadata: a_size, sibling: held_sibling, up: held_up } = unfold(path);
                                            have (a->__rb_parent_color & 1) == 1 by {
                                                rewrite((a->__rb_parent_color & 1), color_bit(color));
                                                rewrite(color_bit(color), 1); normalize();
                                            }
                                            let path = fold(sized_context_at(node, root->rb_node, 0, count), { model: SizedContext::Right(a, gp, color, cached, sibling, up), metadata: a_size, sibling: held_sibling, up: held_up });
                                            let branch_link = fold(sized_flip_chain_root_link(root), { node: old(root->rb_node) });
                                            step(); step(); step();
                                            unfold(branch_link);
                                            have root->rb_node == old(root->rb_node) by close();
                                            have sized_value(focus.model) == count by {
                                                rewrite(focus.model, at(iteration,state.model));
                                                rewrite(at(iteration,state.model), SizedTree::Node(current, above, red, count, lo, hi));
                                                unfold(sized_value(SizedTree::Node(current, above, red, count, lo, hi))); normalize();
                                            }
                                            have sized_parent_is(focus.model, sized_context_parent(path.model, 0)) == 1 by {
                                                rewrite(focus.model, at(iteration,state.model));
                                                rewrite(at(iteration,state.model), SizedTree::Node(current, above, red, count, lo, hi));
                                                unfold(sized_parent_is(SizedTree::Node(current, above, red, count, lo, hi), sized_context_parent(path.model, 0)));
                                                normalize() using { above == sized_context_parent(at(iteration,state.context), 0); at(iteration,state.context) == ctx; ctx == SizedContext::Right(a, gp, color, cached, sibling, up); path.model == SizedContext::Right(a, gp, color, cached, sibling, up); };
                                            }
                                            have sized_plug(path.model, focus.model) == sized_flip_result(at(iteration,state.chain), at(iteration,state.model)) by {
                                                rewrite(at(iteration,state.chain), SizedFlipChain::Stop(ctx));
                                                unfold(sized_flip_result(SizedFlipChain::Stop(ctx), at(iteration,state.model)));
                                                rewrite(focus.model, at(iteration,state.model));
                                                rewrite(path.model, SizedContext::Right(a, gp, color, cached, sibling, up)); rewrite(SizedContext::Right(a, gp, color, cached, sibling, up), ctx); normalize();
                                            }
                                            have above == sized_context_parent(SizedContext::Right(a, gp, color, cached, sibling, up), 0) by {
                                                rewrite(above, parent);
                                                unfold(sized_context_parent(SizedContext::Right(a, gp, color, cached, sibling, up), 0)); close();
                                            }
                                            let state = fold(sized_flip_chain_at(root), {
                                                root_node: old(root->rb_node),
                                                chain: at(iteration,state.chain),
                                                model: SizedTree::Node(current, above, red, count, lo, hi),
                                                context: SizedContext::Right(a, gp, color, cached, sibling, up),
                                                focus: focus, path: path
                                            });
                                            have sized_plug(state.context, state.model) == sized_flip_result(at(iteration,state.chain), at(iteration,state.model)) by close();
                                            have sized_plug(state.context, state.model) == sized_flip_result(old(state.chain), old(state.model)) by close();
                                            step();
                                        },
                                    }
                                },
                            }
                        },
                    }
                }
            }
            mark stopped;
            match state.model {
                SizedTree::Empty => { unfold(state); contradiction(); },
                SizedTree::Node(stopped_node, stopped_parent, stopped_shade, stopped_value, stopped_left, stopped_right) => {
                    let { focus: focus, path: path } = unfold(state);
                    have root->rb_node == old(root->rb_node) by close();
                    have focus.model == SizedTree::Node(stopped_node, stopped_parent, stopped_shade, stopped_value, stopped_left, stopped_right) by close();
                    have sized_value(focus.model) == stopped_value by {
                        rewrite(focus.model, SizedTree::Node(stopped_node, stopped_parent, stopped_shade, stopped_value, stopped_left, stopped_right));
                        unfold(sized_value(SizedTree::Node(stopped_node, stopped_parent, stopped_shade, stopped_value, stopped_left, stopped_right)));
                        normalize();
                    }
                    have stopped_parent == sized_context_parent(path.model, 0) by close();
                    have sized_parent_is(focus.model, sized_context_parent(path.model, 0)) == 1 by {
                        rewrite(focus.model, SizedTree::Node(stopped_node, stopped_parent, stopped_shade, stopped_value, stopped_left, stopped_right));
                        unfold(sized_parent_is(SizedTree::Node(stopped_node, stopped_parent, stopped_shade, stopped_value, stopped_left, stopped_right), sized_context_parent(path.model, 0)));
                        rewrite(sized_context_parent(path.model, 0), stopped_parent);
                        normalize();
                    }
                    have sized_plug(path.model, focus.model) == sized_flip_result(old(state.chain), old(state.model)) by {
                        rewrite(path.model, at(stopped, state.context));
                        rewrite(focus.model, at(stopped, state.model));
                        close();
                    }
                    let root_link = fold(sized_flip_chain_root_link(root), { node: old(root->rb_node) });
                    let { whole: whole } = restore_sized_context(stopped_node, old(root->rb_node), 0, stopped_value, { path: path, sub: focus });
                    step_until(function.exit);
                    unfold(root_link);
                    have root->rb_node == old(root->rb_node) by close();
                    have whole.model == sized_flip_result(old(state.chain), old(state.model)) by close();
                    have sized_parent_is(whole.model, 0) == 1 by close();
                },
            }
        },
    }
}

void insert::__rb_insert_augmented(struct rb_node* node, struct rb_root* root,
                 void (*augment_rotate)(struct rb_node*, struct rb_node*)) {
    consumes state: sized_flip_state(root);
    requires sized_flip_allowed(state.chain) == 1;
    requires state.context == sized_flip_context(state.chain);
    requires node == sized_flip_node(state.model);
    requires sized_flip_color(state.model) == 0;
    requires node->rb_left != node;
    requires node->rb_right != node;
    produces root->rb_node;
    produces whole: sized_at(old(root->rb_node));
    ensures root->rb_node == old(root->rb_node);
    ensures whole.model == sized_flip_result(old(state.chain), old(state.model));
    ensures sized_parent_is(whole.model, 0) == 1;
} by {
    match state.model {
        SizedTree::Empty => { unfold(state); contradiction(); },
        SizedTree::Node(node_id, parent, shade, value, left, right) => {
            let { focus: focus, path: path } = unfold(state);
            have parent == sized_context_parent(path.model, 0) by close();
            let cursor = fold(sized_flip_chain_at(root), {
                root_node: root->rb_node,
                chain: old(state.chain),
                model: SizedTree::Node(node_id, parent, shade, value, left, right),
                context: path.model,
                focus: focus, path: path
            });
            let { whole: whole } = step(insert::__rb_insert, { state: cursor });
            step_until(function.exit);
        },
    }
}

void insert::rb_insert_augmented(struct rb_node* node, struct rb_root* root,
                 const struct rb_augment_callbacks* augment) {
    views augment->rotate;
    consumes state: sized_flip_state(root);
    requires sized_flip_allowed(state.chain) == 1;
    requires state.context == sized_flip_context(state.chain);
    requires node == sized_flip_node(state.model);
    requires sized_flip_color(state.model) == 0;
    requires node->rb_left != node;
    requires node->rb_right != node;
    produces root->rb_node;
    produces whole: sized_at(old(root->rb_node));
    ensures root->rb_node == old(root->rb_node);
    ensures whole.model == sized_flip_result(old(state.chain), old(state.model));
    ensures sized_parent_is(whole.model, 0) == 1;
} by {
    have separate(state, memory(augment->rotate)) by close();
    let { whole: whole } = step(insert::__rb_insert_augmented, { state: state });
}
