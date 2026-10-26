# A retained word frames across a call through a loop alias

The 64-bit companion of
`a_retained_pointer_field_fact_transports_through_a_loop_alias.md`, reduced
from the mirrored rbtree insertion (`__rb_insert`), which keeps a node's
`unsigned long __rb_parent_color` word across `rb_set_parent_color` on another
node. The caller's frame retains `n->word`. With the input opened and re-folded
before the loop, the read after the call is spelled at `n` and the one before
it at `old(n)`; the listed `n == old(n)` makes them one address. The framed-cell
check once required both reads to spell their address identically, so this
transport was refused with "found no frame evidence" however the alias was
listed. It now reads the cell's history at each spelling of the proven-equal
address.

```c filename=retained_word.c
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
verifying "retained_word.c";

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
    step_until(function.exit);
    let after = fold(word_at(m), { tag: 0 });
}

spec enum Anchor {
    At(struct node*, struct node*, struct node*, int32)
}

resource frame(g: struct node*, n: struct node*) {
    field anchor: Anchor;
    match anchor {
        Anchor::At(gg, nn, saved, tag) => {
            fact g == gg;
            fact n == nn;
            fact n->right == saved;
            owns g->left;
            owns g->left->right;
            owns n->left;
            owns n->right;
            owns n->word;
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
        Anchor::At(gg, nn, saved, tag) => {
            let { word: w } = unfold(state);
            let state = fold(frame(g,n), {
                anchor: old(state.anchor)
            }, { word: w });

            loop {
                owns state: frame(g,n);
                invariant state.anchor == Anchor::At(gg, nn, saved, tag);
                invariant n == old(n);
                decreases 0;
                initialize by { assumption(); }
                preserve by {
                    let { word: w } = unfold(state);
                    step(); step(); step(); step(); step(); step();

                    mark before_call;
                    let { after: after } =
                        step(set_word, { w: w });

                    have n->word == at(before_call, n->word) by {
                        transport(at(before_call, n->word) == at(before_call, n->word),
                                  n->word == at(before_call, n->word)) using {
                            n == old(n);
                        };
                    }

                    step(); step();
                }
            }

            step_until(function.exit); assumption();
        },
    }
}
```

```expect
pass
```
