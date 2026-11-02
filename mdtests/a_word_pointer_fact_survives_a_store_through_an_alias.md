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
        transport(at(before, ((g->word & ~3) as (struct node*)) == p), ((g->word & ~3) as (struct node*)) == p) using {
            at(before, ((g->word & ~3) as (struct node*)) == p);
            separate(memory(p->left), memory(g->word));
        };
    }
    step();
}
```

```expect
pass
```
