# A parent alias keeps its child across stores and a call

The parent introduces `p == id` while exposing a named child. The kernel and
surface materializer must use the same checked alias context to name its
pointer field, so the unchanged child can be returned after stores and a call.

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
    produces b: frame(p);
    ensures b.model == old(a.model);
} by {
    match a.model {
        Tag::At(id, cm) => {
            let {kid: kid} = unfold(a);
            have p == id by assumption();
            have separate(memory(q->next), memory(id->other));
            have separate(memory(q->tag), memory(id->other));
            have separate(memory(q->other), memory(id->other));
            mark before_0;
            step();
            have separate(statement(0).footprint, memory(id->other)) by {
                normalize() using { separate(memory(q->next), memory(id->other)); };
            }
            have id->other == at(before_0, id->other) by {
                transport_certificate {
                    premise 0: separate(statement(0).footprint, memory(id->other))
                        => separate(statement(0).footprint, memory(id->other));
                    preserve 0 => id->other == at(before_0, id->other);
                    conclusion 1;
                }
            }
            mark before_1;
            step();
            have separate(statement(1).footprint, memory(id->other)) by {
                normalize() using { separate(memory(q->tag), memory(id->other)); };
            }
            have id->other == at(before_1, id->other) by {
                transport_certificate {
                    premise 0: separate(statement(1).footprint, memory(id->other))
                        => separate(statement(1).footprint, memory(id->other));
                    preserve 0 => id->other == at(before_1, id->other);
                    conclusion 1;
                }
            }
            have id->other == at(before_0, id->other) by {
                transport_certificate {
                    premise 0: id->other == at(before_1, id->other)
                        => id->other == at(before_1, id->other);
                    premise 1: at(before_1, id->other) == at(before_0, id->other)
                        => at(before_1, id->other) == at(before_0, id->other);
                    transitive 0, 1 => id->other == at(before_0, id->other);
                    conclusion 2;
                }
            }
            mark before_2;
            step();
            have separate(statement(2).footprint, memory(id->other)) by {
                normalize() using { separate(memory(q->other), memory(id->other)); };
            }
            have id->other == at(before_2, id->other) by {
                transport_certificate {
                    premise 0: separate(statement(2).footprint, memory(id->other))
                        => separate(statement(2).footprint, memory(id->other));
                    preserve 0 => id->other == at(before_2, id->other);
                    conclusion 1;
                }
            }
            have id->other == at(before_0, id->other) by {
                transport_certificate {
                    premise 0: id->other == at(before_2, id->other)
                        => id->other == at(before_2, id->other);
                    premise 1: at(before_2, id->other) == at(before_0, id->other)
                        => at(before_2, id->other) == at(before_0, id->other);
                    transitive 0, 1 => id->other == at(before_0, id->other);
                    conclusion 2;
                }
            }

            let b = fold(frame(p), {model: Tag::At(id, cm)}, {kid: kid});
            step_until(function.exit); solve();
        },
    }
}
```

```expect
pass
```
