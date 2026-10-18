# Explicit tag arithmetic establishes a logical pointer comparison

Explicit color bounds retain the pointer representation through the C store.
The proof checks the word and mask equations with certificates, then recovers
the original pointer. No smart arithmetic dispatch is needed.
```c filename=roundtrip.c
struct node { unsigned long word; };
void tag(struct node *n, struct node *p, int32 color) {
    n->word = (unsigned long)p | color;
}
```
```click
verifying "roundtrip.c";
theorem direct_roundtrip(p: struct node*) {
    ensures ((struct node*)address(p)) == p by { normalize(); }
}
void tag(struct node* n, struct node* p, int32 color) {
    owns n->word;
    requires aligned(p, 8);
    requires color == 1;
    ensures ((struct node*)(n->word & ~3)) == p;
} by {
    have 0 <= color by { rewrite(color == 1); normalize(); }
    have color <= 1 by { rewrite(color == 1); normalize(); }
    step();
    have n->word == address(p) + 1 by {
        rewrite(color == 1);
        arithmetic_certificate rules {
            premise 0: aligned(p, 8) => aligned(p, 8);
            pointer_word_from_alignment alignments [0] => (address(p) | 1) == address(p) + 1;
            conclusion 0;
        }
    }
    have (n->word & ~3) == address(p) by {
        arithmetic_certificate rules {
            premise 0: aligned(p, 8) => aligned(p, 8);
            pointer_word_from_alignment alignments [0] => (address(p) & ~3) == address(p);
            conclusion 0;
        }
    }
    have ((struct node*)(n->word & ~3)) == p by {
        assumption();
    }
    execute(); simp();
}
```

```expect
pass
```
