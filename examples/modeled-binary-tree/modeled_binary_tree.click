arithmetic "integer";

verifying "modeled_binary_tree.c";

spec enum HeapTree {
    Empty,
    Node(struct tree_node*, int, HeapTree, HeapTree),
}

resource tree_at(p: struct tree_node*) {
    field model: HeapTree;
    match model {
        HeapTree::Empty => { fact p == 0; },
        HeapTree::Node(identity, value, left_model, right_model) => {
            owns *p;
            owns left: tree_at(p->left);
            owns right: tree_at(p->right);
            fact p != 0;
            fact p == identity;
            fact p->value == value;
            fact left.model == left_model;
            fact right.model == right_model;
        },
    }
}

spec enum Context {
    Top,
    Left(struct tree_node*, int, HeapTree, Context),
    Right(struct tree_node*, int, HeapTree, Context),
}

resource ctx_at(child: struct tree_node*) {
    field model: Context;
    match model {
        Context::Top => { },
        Context::Left(parent, value, sibling_model, up_model) => {
            owns parent->value;
            owns parent->left;
            owns parent->right;
            owns sibling: tree_at(parent->right);
            owns up: ctx_at(parent);
            fact parent != 0;
            fact parent->left == child;
            fact parent->value == value;
            fact sibling.model == sibling_model;
            fact up.model == up_model;
        },
        Context::Right(parent, value, sibling_model, up_model) => {
            owns parent->value;
            owns parent->left;
            owns parent->right;
            owns sibling: tree_at(parent->left);
            owns up: ctx_at(parent);
            fact parent != 0;
            fact parent->right == child;
            fact parent->value == value;
            fact sibling.model == sibling_model;
            fact up.model == up_model;
        },
    }
}

function plug(ctx: Context, sub: HeapTree) -> HeapTree
    decreases ctx
{
    match ctx {
        Context::Top => sub,
        Context::Left(parent, value, sibling_model, up_model) =>
            plug(up_model, HeapTree::Node(parent, value, sub, sibling_model)),
        Context::Right(parent, value, sibling_model, up_model) =>
            plug(up_model, HeapTree::Node(parent, value, sibling_model, sub)),
    }
}

theorem plug_top_frame(sub: HeapTree) {
    ensures plug(Context::Top, sub) == sub by {
        unfold(plug(Context::Top, sub));
        normalize();
    }
}

theorem plug_left_frame(parent: struct tree_node*, value: int, sibling: HeapTree,
                        up: Context, sub: HeapTree) {
    ensures plug(Context::Left(parent, value, sibling, up), sub)
        == plug(up, HeapTree::Node(parent, value, sub, sibling)) by {
        unfold(plug(Context::Left(parent, value, sibling, up), sub));
        normalize();
    }
}

theorem plug_right_frame(parent: struct tree_node*, value: int, sibling: HeapTree,
                         up: Context, sub: HeapTree) {
    ensures plug(Context::Right(parent, value, sibling, up), sub)
        == plug(up, HeapTree::Node(parent, value, sibling, sub)) by {
        unfold(plug(Context::Right(parent, value, sibling, up), sub));
        normalize();
    }
}

void tree_node_init(struct tree_node* node, int value,
                    struct tree_node* left, struct tree_node* right) {
    consumes *node;
    consumes l: tree_at(left);
    consumes r: tree_at(right);
    requires node != 0;
    produces root: tree_at(node);
    ensures root.model == HeapTree::Node(node, value, old(l.model), old(r.model));
} by {
    execute();
    let root = fold(tree_at(node), {
        model: HeapTree::Node(node, value, l.model, r.model)
    }, { left: l, right: r });
    simp();
}

function heap_right(tree: HeapTree) -> HeapTree {
    match tree {
        HeapTree::Empty => HeapTree::Empty,
        HeapTree::Node(node, value, left, right) => right,
    }
}

function heap_left(tree: HeapTree) -> HeapTree {
    match tree {
        HeapTree::Empty => HeapTree::Empty,
        HeapTree::Node(node, value, left, right) => left,
    }
}

function heap_rotate_left(tree: HeapTree) -> HeapTree {
    match tree {
        HeapTree::Empty => HeapTree::Empty,
        HeapTree::Node(node, value, left, right) => match right {
            HeapTree::Empty => tree,
            HeapTree::Node(pivot_node, pivot_value, middle, far_right) =>
                HeapTree::Node(pivot_node, pivot_value,
                    HeapTree::Node(node, value, left, middle), far_right),
        },
    }
}

function heap_rotate_right(tree: HeapTree) -> HeapTree {
    match tree {
        HeapTree::Empty => HeapTree::Empty,
        HeapTree::Node(node, value, left, right) => match left {
            HeapTree::Empty => tree,
            HeapTree::Node(pivot_node, pivot_value, far_left, middle) =>
                HeapTree::Node(pivot_node, pivot_value, far_left,
                    HeapTree::Node(node, value, middle, right)),
        },
    }
}

function heap_inorder(tree: HeapTree) -> List<struct tree_node*>
    decreases tree
{
    match tree {
        HeapTree::Empty => List::Nil,
        HeapTree::Node(node, value, left, right) =>
            list::append(heap_inorder(left), List::Cons(node, heap_inorder(right))),
    }
}

function heap_addresses(tree: HeapTree) -> List<uint64>
    decreases tree
{
    match tree {
        HeapTree::Empty => List::Nil,
        HeapTree::Node(node, value, left, right) =>
            list::append(heap_addresses(left), List::Cons(address(node), heap_addresses(right))),
    }
}

function heap_member(tree: HeapTree, target: struct tree_node*) -> bool
    decreases tree
{
    match tree {
        HeapTree::Empty => false,
        HeapTree::Node(node, value, left, right) =>
            if address(node) == address(target) {
                true
            } else {
                if heap_member(left, target) {
                    true
                } else {
                    heap_member(right, target)
                }
            },
    }
}

theorem heap_member_is_address_membership(tree: HeapTree, target: struct tree_node*) {
    ensures heap_member(tree, target) == list::contains(heap_addresses(tree), address(target)) by {
        induct(tree) as ih {
            HeapTree::Empty => {
                unfold(heap_member(HeapTree::Empty, target));
                unfold(heap_addresses(HeapTree::Empty));
                unfold(list::contains(List<uint64>::Nil, address(target)));
                normalize();
            }
            HeapTree::Node(node, value, left, right) => {
                apply(ih(left));
                apply(ih(right));
                unfold(heap_member(HeapTree::Node(node, value, left, right), target));
                unfold(heap_addresses(HeapTree::Node(node, value, left, right)));
                apply(list::contains_append(heap_addresses(left),
                    List::Cons(address(node), heap_addresses(right)), address(target)));
                rewrite(list::contains(list::append(heap_addresses(left),
                    List::Cons(address(node), heap_addresses(right))), address(target))
                    == if list::contains(heap_addresses(left), address(target)) {
                        true
                    } else {
                        list::contains(List::Cons(address(node), heap_addresses(right)), address(target))
                    });
                apply(list::contains_cons(address(node), heap_addresses(right), address(target)));
                rewrite(list::contains(List::Cons(address(node), heap_addresses(right)), address(target))
                    == if address(node) == address(target) {
                        true
                    } else {
                        list::contains(heap_addresses(right), address(target))
                    });
                rewrite(heap_member(left, target) == list::contains(heap_addresses(left), address(target)));
                rewrite(heap_member(right, target) == list::contains(heap_addresses(right), address(target)));
                if address(node) == address(target) {
                    normalize() using { address(node) == address(target); };
                } else {
                    normalize() using { not(address(node) == address(target)); };
                }
            }
        }
    }
}

theorem heap_rotate_left_node_preserves_inorder(node: struct tree_node*, value: int,
                                               left: HeapTree, right: HeapTree) {
    ensures heap_inorder(heap_rotate_left(HeapTree::Node(node, value, left, right)))
        == heap_inorder(HeapTree::Node(node, value, left, right)) by {
        induct(right) as ih {
            HeapTree::Empty => {
                unfold(heap_rotate_left(HeapTree::Node(node, value, left, HeapTree::Empty)));
                normalize();
            }
            HeapTree::Node(pivot, pivot_value, middle, far_right) => {
                unfold(heap_rotate_left(HeapTree::Node(node, value, left,
                    HeapTree::Node(pivot, pivot_value, middle, far_right))));
                unfold(heap_inorder(HeapTree::Node(pivot, pivot_value,
                    HeapTree::Node(node, value, left, middle), far_right)));
                unfold(heap_inorder(HeapTree::Node(node, value, left,
                    HeapTree::Node(pivot, pivot_value, middle, far_right))));
                unfold(heap_inorder(HeapTree::Node(node, value, left, middle)));
                unfold(heap_inorder(HeapTree::Node(pivot, pivot_value, middle, far_right)));
                apply(list::append_associative(heap_inorder(left),
                    List::Cons(node, heap_inorder(middle)),
                    List::Cons(pivot, heap_inorder(far_right))));
                rewrite(list::append(list::append(heap_inorder(left),
                    List::Cons(node, heap_inorder(middle))),
                    List::Cons(pivot, heap_inorder(far_right)))
                    == list::append(heap_inorder(left),
                        list::append(List::Cons(node, heap_inorder(middle)),
                            List::Cons(pivot, heap_inorder(far_right)))));
                unfold(list::append(List::Cons(node, heap_inorder(middle)),
                    List::Cons(pivot, heap_inorder(far_right))));
                normalize();
            }
        }
    }
}

theorem heap_rotate_left_preserves_inorder(tree: HeapTree) {
    ensures heap_inorder(heap_rotate_left(tree)) == heap_inorder(tree) by {
        induct(tree) as ih {
            HeapTree::Empty => {
                unfold(heap_rotate_left(HeapTree::Empty));
                normalize();
            }
            HeapTree::Node(node, value, left, right) => {
                apply(heap_rotate_left_node_preserves_inorder(node, value, left, right));
                assumption();
            }
        }
    }
}

theorem heap_rotate_right_node_preserves_inorder(node: struct tree_node*, value: int,
                                                 left: HeapTree, right: HeapTree) {
    ensures heap_inorder(heap_rotate_right(HeapTree::Node(node, value, left, right)))
        == heap_inorder(HeapTree::Node(node, value, left, right)) by {
        induct(left) as ih {
            HeapTree::Empty => {
                unfold(heap_rotate_right(HeapTree::Node(node, value, HeapTree::Empty, right)));
                normalize();
            }
            HeapTree::Node(pivot, pivot_value, far_left, middle) => {
                unfold(heap_rotate_right(HeapTree::Node(node, value,
                    HeapTree::Node(pivot, pivot_value, far_left, middle), right)));
                unfold(heap_inorder(HeapTree::Node(pivot, pivot_value, far_left,
                    HeapTree::Node(node, value, middle, right))));
                unfold(heap_inorder(HeapTree::Node(node, value,
                    HeapTree::Node(pivot, pivot_value, far_left, middle), right)));
                unfold(heap_inorder(HeapTree::Node(node, value, middle, right)));
                unfold(heap_inorder(HeapTree::Node(pivot, pivot_value, far_left, middle)));
                apply(list::append_associative(heap_inorder(far_left),
                    List::Cons(pivot, heap_inorder(middle)),
                    List::Cons(node, heap_inorder(right))));
                rewrite(list::append(list::append(heap_inorder(far_left),
                    List::Cons(pivot, heap_inorder(middle))),
                    List::Cons(node, heap_inorder(right)))
                    == list::append(heap_inorder(far_left),
                        list::append(List::Cons(pivot, heap_inorder(middle)),
                            List::Cons(node, heap_inorder(right)))));
                unfold(list::append(List::Cons(pivot, heap_inorder(middle)),
                    List::Cons(node, heap_inorder(right))));
                normalize();
            }
        }
    }
}

theorem heap_rotate_right_preserves_inorder(tree: HeapTree) {
    ensures heap_inorder(heap_rotate_right(tree)) == heap_inorder(tree) by {
        induct(tree) as ih {
            HeapTree::Empty => {
                unfold(heap_rotate_right(HeapTree::Empty));
                normalize();
            }
            HeapTree::Node(node, value, left, right) => {
                apply(heap_rotate_right_node_preserves_inorder(node, value, left, right));
                assumption();
            }
        }
    }
}

theorem plug_inorder_transport(ctx: Context, a: HeapTree, b: HeapTree) {
    requires heap_inorder(a) == heap_inorder(b);
    ensures heap_inorder(plug(ctx, a)) == heap_inorder(plug(ctx, b)) by {
        induct(ctx) as ih {
            Context::Top => {
                unfold(plug(Context::Top, a));
                unfold(plug(Context::Top, b));
                assumption();
            }
            Context::Left(parent, value, sibling, up) => {
                have heap_inorder(HeapTree::Node(parent, value, a, sibling))
                    == heap_inorder(HeapTree::Node(parent, value, b, sibling)) by {
                    unfold(heap_inorder(HeapTree::Node(parent, value, a, sibling)));
                    unfold(heap_inorder(HeapTree::Node(parent, value, b, sibling)));
                    rewrite(heap_inorder(a) == heap_inorder(b));
                    normalize();
                }
                apply(ih(up, HeapTree::Node(parent, value, a, sibling),
                         HeapTree::Node(parent, value, b, sibling)));
                unfold(plug(Context::Left(parent, value, sibling, up), a));
                unfold(plug(Context::Left(parent, value, sibling, up), b));
                assumption();
            }
            Context::Right(parent, value, sibling, up) => {
                have heap_inorder(HeapTree::Node(parent, value, sibling, a))
                    == heap_inorder(HeapTree::Node(parent, value, sibling, b)) by {
                    unfold(heap_inorder(HeapTree::Node(parent, value, sibling, a)));
                    unfold(heap_inorder(HeapTree::Node(parent, value, sibling, b)));
                    rewrite(heap_inorder(a) == heap_inorder(b));
                    normalize();
                }
                apply(ih(up, HeapTree::Node(parent, value, sibling, a),
                         HeapTree::Node(parent, value, sibling, b)));
                unfold(plug(Context::Right(parent, value, sibling, up), a));
                unfold(plug(Context::Right(parent, value, sibling, up), b));
                assumption();
            }
        }
    }
}

struct tree_node* tree_rotate_left(struct tree_node* root) {
    consumes t: tree_at(root);
    requires t.model != HeapTree::Empty;
    requires heap_right(t.model) != HeapTree::Empty;
    produces rotated: tree_at(result);
    ensures rotated.model == heap_rotate_left(old(t.model));
    ensures heap_inorder(rotated.model) == heap_inorder(old(t.model));
} by {
    match t.model {
        HeapTree::Empty => { contradiction(t.model == HeapTree::Empty); },
        HeapTree::Node(node, value, left_model, right_model) => {
            have heap_right(t.model) == right_model by auto();
            have right_model != HeapTree::Empty by auto();
            match right_model {
                HeapTree::Empty => { contradiction(right_model == HeapTree::Empty); },
                HeapTree::Node(pivot_node, pivot_value, middle_model, far_right_model) => {
                    let { left: left, right: r } = unfold(t);
                    let { left: m, right: right } = unfold(r);
                    execute();
                    let lower = fold(tree_at(root), {
                        model: HeapTree::Node(node, value, left_model, middle_model)
                    }, { right: m });
                    let rotated = fold(tree_at(result), {
                        model: HeapTree::Node(pivot_node, pivot_value,
                            HeapTree::Node(node, value, left_model, middle_model), far_right_model)
                    }, { left: lower });
                    apply(heap_rotate_left_preserves_inorder(old(t.model)));
                },
            }
        },
    }
}

struct tree_node* tree_rotate_right(struct tree_node* root) {
    consumes t: tree_at(root);
    requires t.model != HeapTree::Empty;
    requires heap_left(t.model) != HeapTree::Empty;
    produces rotated: tree_at(result);
    ensures rotated.model == heap_rotate_right(old(t.model));
    ensures heap_inorder(rotated.model) == heap_inorder(old(t.model));
} by {
    match t.model {
        HeapTree::Empty => { contradiction(t.model == HeapTree::Empty); },
        HeapTree::Node(node, value, left_model, right_model) => {
            have heap_left(t.model) == left_model by auto();
            have left_model != HeapTree::Empty by auto();
            match left_model {
                HeapTree::Empty => { contradiction(left_model == HeapTree::Empty); },
                HeapTree::Node(pivot_node, pivot_value, far_left_model, middle_model) => {
                    let { left: l, right: right } = unfold(t);
                    let { left: left, right: m } = unfold(l);
                    execute();
                    let lower = fold(tree_at(root), {
                        model: HeapTree::Node(node, value, middle_model, right_model)
                    }, { left: m });
                    let rotated = fold(tree_at(result), {
                        model: HeapTree::Node(pivot_node, pivot_value, far_left_model,
                            HeapTree::Node(node, value, middle_model, right_model))
                    }, { right: lower });
                    apply(heap_rotate_right_preserves_inorder(old(t.model)));
                },
            }
        },
    }
}

int tree_contains(struct tree_node* root, struct tree_node* target) {
    owns t: tree_at(root);
    decreases t;
    ensures t.model == old(t.model);
    ensures result == heap_member(old(t.model), target);
} by {
    match t.model {
        HeapTree::Empty => {
            unfold(t);
            execute();
            let t = fold(tree_at(root), { model: HeapTree::Empty });
            simp();
        },
        HeapTree::Node(node, value, left_model, right_model) => {
            let { left: l, right: r } = unfold(t);
            branch { step(); simp(); } else {}
            branch {
                step();
                let t = fold(tree_at(root), { model: old(t.model) }, { left: l, right: r });
                have address(node) == address(target) by auto();
                simp();
            } else {}
            have not(address(node) == address(target)) by {
                rewrite(node == root);
                normalize() using { address(root) != address(target); };
            }
            let { result: found_left } = step(tree_contains(root->left, target), { t: l });
            branch {
                step();
                have heap_member(left_model, target) by {
                    have left_model == l.model by {
                        rewrite(l.model == left_model);
                        normalize();
                    }
                    have heap_member(l.model, target) != false by auto();
                    rewrite(left_model == l.model);
                    assumption();
                }
                let t = fold(tree_at(root), { model: old(t.model) }, { left: l, right: r });
                simp();
            } else {}
            have heap_member(left_model, target) == 0 by {
                simp() using {
                    found_left == 0;
                    found_left == heap_member(left_model, target);
                };
            }
            let { result: found_right } = step(tree_contains(root->right, target), { t: r });
            step();
            let t = fold(tree_at(root), { model: old(t.model) }, { left: l, right: r });
            have result == heap_member(old(t.model), target) by {
                rewrite(old(t.model)
                    == HeapTree::Node(node, value, left_model, right_model));
                unfold(heap_member(
                    HeapTree::Node(node, value, left_model, right_model), target));
                rewrite(heap_member(left_model, target) == false);
                rewrite(result == heap_member(right_model, target));
                normalize() using { not(address(node) == address(target)); };
            }
            simp();
        },
    }
}

struct tree_node* tree_leftmost(struct tree_node* root) {
    consumes t: tree_at(root);
    requires t.model != HeapTree::Empty;
    produces ctx: ctx_at(result);
    produces sub: tree_at(result);
    ensures plug(ctx.model, sub.model) == old(t.model);
    ensures heap_left(sub.model) == HeapTree::Empty;
} by {
    step();
    step();
    let ctx = fold(ctx_at(root), { model: Context::Top });
    loop {
        owns ctx: ctx_at(root);
        owns t: tree_at(root);
        decreases t;
        invariant t.model != HeapTree::Empty;
        invariant plug(ctx.model, t.model) == old(t.model);

        initialize by simp();
        preserve by {
            match t.model {
                HeapTree::Empty => { contradiction(t.model == HeapTree::Empty); },
                HeapTree::Node(identity, value, left_model, right_model) => {
                    have plug(Context::Left(identity, value, right_model, ctx.model), left_model)
                        == old(t.model) by {
                        unfold(plug(Context::Left(identity, value, right_model, ctx.model),
                            left_model));
                        rewrite(HeapTree::Node(identity, value, left_model, right_model) == t.model);
                        assumption();
                    }
                    let { left: l, right: rt } = unfold(t);
                    have plug(Context::Left(root, value, right_model, ctx.model), left_model)
                        == old(t.model) by {
                        rewrite(root == identity);
                        assumption();
                    }
                    let frame = fold(ctx_at(root->left), {
                        model: Context::Left(root, value, right_model, ctx.model)
                    }, { sibling: rt, up: ctx });
                },
            }
        }
    }
    match t.model {
        HeapTree::Empty => { contradiction(t.model == HeapTree::Empty); },
        HeapTree::Node(identity, value, left_model, right_model) => {
            have plug(ctx.model, HeapTree::Node(identity, value, left_model, right_model))
                == old(t.model) by {
                rewrite(HeapTree::Node(identity, value, left_model, right_model) == t.model);
                assumption();
            }
            let { left: l, right: rt } = unfold(t);
            have heap_left(HeapTree::Node(identity, value, left_model, right_model))
                == left_model by {
                unfold(heap_left(HeapTree::Node(identity, value, left_model, right_model)));
                normalize();
            }
            let sub = fold(tree_at(root), {
                model: HeapTree::Node(identity, value, left_model, right_model)
            }, { left: l, right: rt });
            step();
            simp();
        },
    }
}

struct tree_node* tree_rightmost(struct tree_node* root) {
    consumes t: tree_at(root);
    requires t.model != HeapTree::Empty;
    produces ctx: ctx_at(result);
    produces sub: tree_at(result);
    ensures plug(ctx.model, sub.model) == old(t.model);
    ensures heap_right(sub.model) == HeapTree::Empty;
} by {
    step();
    step();
    let ctx = fold(ctx_at(root), { model: Context::Top });
    loop {
        owns ctx: ctx_at(root);
        owns t: tree_at(root);
        decreases t;
        invariant t.model != HeapTree::Empty;
        invariant plug(ctx.model, t.model) == old(t.model);

        initialize by simp();
        preserve by {
            match t.model {
                HeapTree::Empty => { contradiction(t.model == HeapTree::Empty); },
                HeapTree::Node(identity, value, left_model, right_model) => {
                    have plug(Context::Right(identity, value, left_model, ctx.model), right_model)
                        == old(t.model) by {
                        unfold(plug(Context::Right(identity, value, left_model, ctx.model),
                            right_model));
                        rewrite(HeapTree::Node(identity, value, left_model, right_model) == t.model);
                        assumption();
                    }
                    let { left: l, right: rt } = unfold(t);
                    have plug(Context::Right(root, value, left_model, ctx.model), right_model)
                        == old(t.model) by {
                        rewrite(root == identity);
                        assumption();
                    }
                    let frame = fold(ctx_at(root->right), {
                        model: Context::Right(root, value, left_model, ctx.model)
                    }, { sibling: l, up: ctx });
                },
            }
        }
    }
    match t.model {
        HeapTree::Empty => { contradiction(t.model == HeapTree::Empty); },
        HeapTree::Node(identity, value, left_model, right_model) => {
            have plug(ctx.model, HeapTree::Node(identity, value, left_model, right_model))
                == old(t.model) by {
                rewrite(HeapTree::Node(identity, value, left_model, right_model) == t.model);
                assumption();
            }
            let { left: l, right: rt } = unfold(t);
            have heap_right(HeapTree::Node(identity, value, left_model, right_model))
                == right_model by {
                unfold(heap_right(HeapTree::Node(identity, value, left_model, right_model)));
                normalize();
            }
            let sub = fold(tree_at(root), {
                model: HeapTree::Node(identity, value, left_model, right_model)
            }, { left: l, right: rt });
            step();
            simp();
        },
    }
}

spec enum Tree<T> {
    Empty,
    Node(Tree<T>, T, Tree<T>),
}

function tree_size<T>(tree: Tree<T>) -> Nat
    decreases tree
{
    match tree {
        Tree::Empty => Nat::Zero,
        Tree::Node(left, value, right) =>
            Nat::Succ(nat::add(tree_size(left), tree_size(right))),
    }
}

function tree_mirror<T>(tree: Tree<T>) -> Tree<T>
    decreases tree
{
    match tree {
        Tree::Empty => Tree::Empty,
        Tree::Node(left, value, right) =>
            Tree::Node(tree_mirror(right), value, tree_mirror(left)),
    }
}

theorem tree_mirror_twice<T>(tree: Tree<T>) {
    ensures tree_mirror(tree_mirror(tree)) == tree by {
        induct(tree) as ih {
            Tree::Empty => {
                unfold(tree_mirror(Tree<T>::Empty));
                simp();
            }
            Tree::Node(left, value, right) => {
                apply(ih(left));
                apply(ih(right));
                unfold(tree_mirror(Tree::Node(left, value, right)));
                unfold(tree_mirror(Tree::Node(tree_mirror(right), value, tree_mirror(left))));
                rewrite(tree_mirror(tree_mirror(left)) == left);
                rewrite(tree_mirror(tree_mirror(right)) == right);
                normalize();
            }
        }
    }
}

theorem tree_mirror_preserves_size<T>(tree: Tree<T>) {
    ensures tree_size(tree_mirror(tree)) == tree_size(tree) by {
        induct(tree) as ih {
            Tree::Empty => {
                unfold(tree_mirror(Tree<T>::Empty));
                normalize();
            }
            Tree::Node(left, value, right) => {
                apply(ih(left));
                apply(ih(right));
                unfold(tree_mirror(Tree::Node(left, value, right)));
                unfold(tree_size(Tree::Node(tree_mirror(right), value, tree_mirror(left))));
                unfold(tree_size(Tree::Node(left, value, right)));
                rewrite(tree_size(tree_mirror(left)) == tree_size(left));
                rewrite(tree_size(tree_mirror(right)) == tree_size(right));
                apply(nat::add_commutative(tree_size(right), tree_size(left)));
                rewrite(nat::add(tree_size(right), tree_size(left))
                    == nat::add(tree_size(left), tree_size(right)));
                normalize();
            }
        }
    }
}
