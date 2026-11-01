# Pointer history removal: integer-address congruence reduction

```c filename=packed.c
struct node { unsigned long word; unsigned long tag; };
void update(struct node *q) { q->tag = 1; }
struct node *caller(struct node *p, struct node *q, struct node *parent) {
    update(q);
    return (struct node *)(p->word & ~3);
}
```

```click
verifying "packed.c";
void update(struct node *q) { owns q->tag; } by { step(); step(); solve(); }
struct node *caller(struct node *p, struct node *q, struct node *parent) {
    owns p->word;
    owns q->tag;
    requires ((p->word & ~3) as (struct node *)) == parent;
    requires separate(memory(p->word), memory(q->tag));
    ensures result == parent;
} by {
    mark before;
    step();
    have separate(statement(0).footprint, memory(p->word)) by {
        normalize() using { separate(memory(p->word), memory(q->tag)); };
    }
    have p->word == at(before, p->word) by {
        transport_certificate {
            premise 0: separate(statement(0).footprint, memory(p->word))
                => separate(statement(0).footprint, memory(p->word));
            preserve 0 => p->word == at(before, p->word);
            conclusion 1;
        }
    }
    have ((p->word & ~3) as (struct node *)) == parent by {
        rewrite(p->word == at(before, p->word));
        assumption();
    }
    step();
    assumption();
}
```

```expect
pass
```
