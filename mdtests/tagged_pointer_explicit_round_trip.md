# Explicit tag arithmetic establishes a logical pointer comparison

Arithmetic search expands to ordinary proof steps, with the selected premises
stated explicitly in `solve() using { ... }`.

```c filename=roundtrip.c
struct node { unsigned long word; };
void tag(struct node *n, struct node *p, int32 color) {
    n->word = (unsigned long)p | color;
}
```
```click
verifying "roundtrip.c";
theorem direct_roundtrip(p: struct node*) {
    ensures (address(p) as (struct node *)) == p by { known(); }
}
void tag(struct node* n, struct node* p, int32 color) {
    owns n->word;
    requires aligned(p, 8);
    requires color == 1;
    ensures ((n->word & ~3) as (struct node *)) == p;
} by {
    have 0 <= color by { rewrite(color, 1); known(); }
    have color <= 1 by { rewrite(color, 1); known(); }
    step();
    have n->word == address(p) + 1 by {
        rewrite(color, 1);
        solve() using { aligned(p, 8); };
    }
    have (n->word & ~3) == address(p) by {
        rewrite(color, 1);
        solve() using { aligned(p, 8); };
    }
    have ((n->word & ~3) as (struct node *)) == p by {
        known();
    }
}
```

```expect
pass
```
