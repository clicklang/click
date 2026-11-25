# Explicit tag arithmetic establishes a logical pointer comparison

Arithmetic search expands to ordinary proof steps, with the selected premises
stated explicitly in `close() using { ... }`.

```c filename=roundtrip.c
struct node { unsigned long word; };
void tag(struct node *n, struct node *p, int32 color) {
    n->word = (unsigned long)p | color;
}
```
```click
verifying "roundtrip.c";
theorem direct_roundtrip(p: struct node*) {
    ensures (address(p) as (struct node *)) == p by { close(); }
}
void tag(struct node* n, struct node* p, int32 color) {
    owns n->word;
    requires aligned(p, 8);
    requires color == 1;
    ensures ((n->word & ~3) as (struct node *)) == p;
} by {
    have 0 <= color by { rewrite(color, 1); close(); }
    have color <= 1 by { rewrite(color, 1); close(); }
    step();
    have n->word == address(p) + 1 by {
        rewrite(color, 1);
        close() using { aligned(p, 8); };
    }
    have (n->word & ~3) == address(p) by {
        rewrite(n->word, address(p) + 1);
        have (address(p) & 3u64) == 0u64 by { close() using { aligned(p, 8); }; }
        apply(click::integer::uint64_mask_add_clear(address(p), 1u64, ~3u64));
    }
    have ((n->word & ~3) as (struct node *)) == p by {
        close();
    }
}
```

```expect
pass
```
