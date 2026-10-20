verifying "rbtree-retained-child-read.c";
resource word_at(p: struct node*) { field tag: int32; owns p->word; fact tag == 0; }
void set_word(struct node* m, struct node* p) {
    consumes w: word_at(m);
    produces after: word_at(m);
    ensures true;
} by { unfold(w); execute(); let after = fold(word_at(m), { tag: 0 }); }
spec enum Anchor { At(struct node*, struct node*, int32) }
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
    // These two steps are essential to the refusal. Removing both lets the
    // later read-transport link pass, with the C and remaining proof unchanged.
    let { word: w } = unfold(state);
    let state = fold(frame(g,n), { anchor: old(state.anchor) }, { word: w });
    loop {
        owns state: frame(g,n);
        invariant state.anchor == Anchor::At(gg, nn, tag);
        invariant n == old(n);
        initialize by { assumption(); }
        preserve by {
            let { word: w } = unfold(state);
            step(); step(); step(); step(); step(); step();
            mark before_call;
            let { after: after } = step(set_word(tmp,p), { w: w });
            have n == old(n) by { assumption(); }
            have n->right == at(before_call,n->right) by {
                transport(at(before_call,n->right) == at(before_call,n->right),
                          n->right == at(before_call,n->right)) using {
                    n == old(n);
                };
            }
            execute(); assumption();
        }
    }
    execute(); assumption();
      },
    }
}
