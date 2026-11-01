# Field separation uses the imported ABI width

The helper writes an eight-byte tag. Its separation from the retained pointer
field must cover all eight bytes, including when unfolding a named child
introduced another name for the parent.

```c filename=probe.c
struct node { unsigned long tag; struct node *other; struct node *next; };
void helper(struct node *q) { q->tag = 0; }
void probe(struct node *p, struct node *q) { q->next = p; helper(q); q->other = p; }
```

```click
verifying "probe.c";
spec enum Tag { At(struct node*, Child) }
spec enum Child { Empty }
resource child(p: struct node*) { field model: Child; owns p->tag; }
resource frame(p: struct node*) {
    field model: Tag;
    match model {
        Tag::At(id, cm) => {
            owns id->other;
            owns kid: child(id->other);
            fact kid.model == cm;
            fact p == id;
        },
    }
}
void helper(struct node *q) { owns q->tag; } by { step_until(function.exit); solve(); }
void probe(struct node *p, struct node *q) {
    owns q->tag; owns q->next; owns q->other;
    consumes a: frame(p);
    requires separate(memory(p->other), memory(q->next));
    requires separate(memory(p->other), memory(q->other));
    requires separate(memory(p->other), memory(q->tag));
} by {
    match a.model {
        Tag::At(id, cm) => {
            let {kid: kid} = unfold(a);
            have p == id by assumption();
            step();
            have separate(memory(p->other), memory(q->tag));
            mark before;
            step();
            have separate(statement(1).footprint, memory(p->other)) by {
                normalize() using { separate(memory(p->other), memory(q->tag)); };
            }
            have p->other == at(before, p->other) by {
                transport_certificate {
                    premise 0: separate(statement(1).footprint, memory(p->other))
                        => separate(statement(1).footprint, memory(p->other));
                    preserve 0 => p->other == at(before, p->other);
                    conclusion 1;
                }
            }
            mark after_call;
            step();
            have separate(statement(2).footprint, memory(p->other)) by {
                normalize() using { separate(memory(p->other), memory(q->other)); };
            }
            have p->other == at(after_call, p->other) by {
                transport_certificate {
                    premise 0: separate(statement(2).footprint, memory(p->other))
                        => separate(statement(2).footprint, memory(p->other));
                    preserve 0 => p->other == at(after_call, p->other);
                    conclusion 1;
                }
            }
            have p->other == at(before, p->other) by {
                transport_certificate {
                    premise 0: p->other == at(after_call, p->other)
                        => p->other == at(after_call, p->other);
                    premise 1: at(after_call, p->other) == at(before, p->other)
                        => at(after_call, p->other) == at(before, p->other);
                    transitive 0, 1 => p->other == at(before, p->other);
                    conclusion 2;
                }
            }
            step_until(function.exit); solve();
        },
    }
}
```

```expect
pass
```
