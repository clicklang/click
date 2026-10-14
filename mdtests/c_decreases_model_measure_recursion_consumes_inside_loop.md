# a recursive call inside a ranked loop may consume a child and free its node

`destroy` releases a left-child, right-sibling tree: the loop walks the
siblings, and each iteration recursively destroys the child subtree and frees
the node. The recursive call consumes the child `c` it unfolded, and its
descent is owed against `destroy`'s entry reading of `tree_size(x.model)`: the
loop invariant keeps the current subtree no larger than the entry tree, so the
child is strictly smaller. The loop binder then moves to the sibling, and the
freed node's tombstone is the only heap difference at the back edge.

```c filename=c_decreases_model_measure_recursion_consumes_inside_loop.c
struct tree {
    struct tree *child;
    struct tree *sibling;
};

void destroy(struct tree *t) {
    while (t != 0) {
        struct tree *next = t->sibling;
        destroy(t->child);
        free(t);
        t = next;
    }
}
```

```click
verifying "c_decreases_model_measure_recursion_consumes_inside_loop.c";

spec enum Tree { Leaf, Node(Tree, Tree) }

function tree_size(m: Tree) -> Integer
    decreases m
{
    match m {
        Tree::Leaf => 0,
        Tree::Node(child, sibling) => tree_size(child) + tree_size(sibling) + 1,
    }
}

theorem tree_size_is_nonnegative(m: Tree) {
    ensures 0 <= tree_size(m) by {
        induct(m) as ih {
            Tree::Leaf => {
                unfold(tree_size(Tree::Leaf));
                normalize();
            }
            Tree::Node(child, sibling) => {
                apply(ih(child));
                apply(ih(sibling));
                unfold(tree_size(Tree::Node(child, sibling)));
                arithmetic() using {
                    0 <= tree_size(child);
                    0 <= tree_size(sibling);
                }
            }
        }
    }
}

resource tree_at(t: struct tree*) {
    field model: Tree;
    match model {
        Tree::Leaf => { fact t == 0; },
        Tree::Node(child_model, sibling_model) => {
            owns allocation(t, sizeof(struct tree));
            owns *t;
            owns child: tree_at(t->child);
            owns sibling: tree_at(t->sibling);
            fact t != 0;
            fact child.model == child_model;
            fact sibling.model == sibling_model;
        },
    }
}

void destroy(struct tree* t) {
    consumes x: tree_at(t);
    decreases tree_size(x.model);
} by {
    loop {
        owns x: tree_at(t);
        decreases tree_size(x.model);
        invariant tree_size(x.model) <= tree_size(old(x.model));

        initialize by simp;
        preserve by {
            match x.model {
                Tree::Leaf => { contradiction(x.model == Tree::Leaf); },
                Tree::Node(child_model, sibling_model) => {
                    apply(tree_size_is_nonnegative(child_model));
                    apply(tree_size_is_nonnegative(sibling_model));
                    have tree_size(x.model) == tree_size(child_model) + tree_size(sibling_model) + 1 by {
                        rewrite(x.model == Tree::Node(child_model, sibling_model));
                        unfold(tree_size(Tree::Node(child_model, sibling_model)));
                        normalize();
                    }
                    have tree_size(child_model) < tree_size(old(x.model)) by {
                        arithmetic() using {
                            tree_size(x.model) == tree_size(child_model) + tree_size(sibling_model) + 1;
                            tree_size(x.model) <= tree_size(old(x.model));
                            0 <= tree_size(sibling_model);
                        }
                    }
                    have tree_size(sibling_model) < tree_size(x.model) by {
                        arithmetic() using {
                            tree_size(x.model) == tree_size(child_model) + tree_size(sibling_model) + 1;
                            0 <= tree_size(child_model);
                        }
                    }
                    have tree_size(sibling_model) <= tree_size(old(x.model)) by {
                        arithmetic() using {
                            tree_size(sibling_model) < tree_size(x.model);
                            tree_size(x.model) <= tree_size(old(x.model));
                        }
                    }
                    let { child: c, sibling: s } = unfold(x);
                    have 0 <= tree_size(c.model) by {
                        rewrite(c.model == child_model);
                        assumption();
                    }
                    have tree_size(c.model) < tree_size(old(x.model)) by {
                        rewrite(c.model == child_model);
                        assumption();
                    }
                    have tree_size(s.model) <= tree_size(old(x.model)) by {
                        rewrite(s.model == sibling_model);
                        assumption();
                    }
                    have 0 <= tree_size(s.model) by {
                        rewrite(s.model == sibling_model);
                        assumption();
                    }
                    step();
                    step();
                    step(destroy(t->child), { x: c });
                    step();
                    step();
                    close_invariants();
                },
            }
        }
    }
    unfold(x);
    step();
    simp();
}
```

```expect
pass
```
