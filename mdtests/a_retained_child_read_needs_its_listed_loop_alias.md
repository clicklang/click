# A retained child read needs its listed loop alias

The companion of `a_retained_child_read_frames_across_a_call_through_a_loop_alias.md`
without the `using` premise `n == old(n)`. The two reads' addresses are then
not known to be one cell, so the same transport is refused.

```c filename=retained_child_read_unlisted.c
struct node {
    unsigned long word;
    struct node *right;
    struct node *left;
};

void set_word(struct node *m, struct node *p) {
    m->word = (unsigned long)p | 1;
}

void probe(struct node *g, struct node *n) {
    while (1) {
        struct node *p = g->left;
        struct node *tmp = n->left;
        p->right = tmp;
        n->left = p;
        set_word(tmp, p);
        n = p;
        break;
    }
}
```

```click
verifying "retained_child_read_unlisted.c";

resource word_at(p: struct node*) {
    field tag: int32;
    owns p->word;
    fact tag == 0;
}

void set_word(struct node* m, struct node* p) {
    consumes w: word_at(m);
    produces after: word_at(m);
    ensures true;
} by {
    unfold(w);
    execute();
    let after = fold(word_at(m), { tag: 0 });
}

spec enum Anchor {
    At(struct node*, struct node*, int32)
}

resource frame(g: struct node*, n: struct node*) {
    field anchor: Anchor;
    match anchor {
        Anchor::At(gg, nn, tag) => {
            fact g == gg;
            fact n == nn;
            owns g->left;
            owns g->left->right;
            owns n->left;
            owns n->right;
            owns word: word_at(n->left);
            fact word.tag == tag;
            fact g->left != 0;
            fact n->left != 0;
        },
    }
}

void probe(struct node* g, struct node* n) {
    consumes state: frame(g,n);
    ensures true;
} by {
    match state.anchor {
        Anchor::At(gg, nn, tag) => {
            // Opening and re-folding the input before the loop is what once
            // made the transport below refuse.
            let { word: w } = unfold(state);
            let state = fold(frame(g,n), {
                anchor: old(state.anchor)
            }, { word: w });

            loop {
                owns state: frame(g,n);
                invariant state.anchor == Anchor::At(gg, nn, tag);
                invariant n == old(n);
                decreases 0;
                initialize by { assumption(); }
                preserve by {
                    let { word: w } = unfold(state);
                    step(); step(); step(); step(); step(); step();

                    mark before_call;
                    let { after: after } =
                        step(set_word(tmp,p), { w: w });

                    have n == old(n) by { assumption(); }

                    have n->right == at(before_call,n->right) by {
                        transport(
                            at(before_call,n->right)
                                == at(before_call,n->right),
                            n->right == at(before_call,n->right)
                        ) using {
                        };
                    }

                    step(); step();
                }
            }

            execute(); assumption();
        },
    }
}
```

```expect
fail: `transport using` found no frame evidence carrying its source fact to the target's state
```
