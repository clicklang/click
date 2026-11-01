# A rewritten tagged null pointer normalizes

```c filename=tag.c
struct node { unsigned long word; };
void tag(struct node *n) { n->word = 1; }
```

```click
verifying "tag.c";
void tag(struct node* n) {
    owns n->word;
    ensures ((n->word & ~3) as (struct node *)) == 0;
} by {
    step();
    have n->word == 1 by { assumption(); }
    have ((n->word & ~3) as (struct node *)) == 0 by {
        rewrite(n->word == 1);
        normalize();
    }
    step();
    solve();
}
```

```expect
pass
```
