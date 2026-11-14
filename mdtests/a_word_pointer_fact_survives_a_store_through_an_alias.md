# A reconstructed pointer survives a separate store through an alias

The word and its pointer identity survive the same checked store. Observing
the struct fields at entry must not prevent the pointer frame from connecting
the store to the read's earlier source.

```c filename=parent_word.c
struct node { unsigned long word; struct node *right; struct node *left; };
void update(struct node *g, struct node *p) {
    p->left = g;
}
```

```click
verifying "parent_word.c";
void update(struct node *g, struct node *p) {
    owns *g;
    requires g == p;
    requires ((g->word & ~3) as (struct node*)) == p;
} by {
    mark before;
    have separate(memory(p->left), memory(g->word)) by { solve(); }
    step();
    have ((g->word & ~3) as (struct node*)) == p by {
        have separate(statement(0).footprint, memory(g->word)) by {
            normalize() using { separate(memory(p->left), memory(g->word)); };
        }
        have g->word == at(before, g->word) by {
            preserve(separate(statement(0).footprint, memory(g->word)));
        }
        have *((&g->word) as (int32 **)) == at(before, *((&g->word) as (int32 **))) by {
            preserve(separate(statement(0).footprint, memory(g->word)));
        }
        rewrite(g->word == at(before, g->word));
        assumption();
    }
    step();
}
```

```expect
pass
```
