# a tagged address word survives a call framing its neighbour

A function stores a pointer's address with its low bit set into a `uint64`
field, then calls a function that owns only the neighbouring field. A fact
about the word recorded before the call, named through the resource model's
identity rather than the C parameter, still holds after the call: the load is
preserved across the call by an explicit read equality, then rewritten through
the wide bitwise-or. The proof uses the call's footprint containment and the
separation of the two fields, without recovering the tagged value from memory.

```c filename=a_tagged_address_word_survives_a_call_framing_its_neighbour.c
struct node { uint64 tag; uint64 count; };

void set_count(struct node *p) { p->count = 1; }

void tag_then_count(struct node *p) {
    while (true) {
        p->tag = (uint64)p | 1;
        set_count(p);
        break;
    }
}
```

```click
verifying "a_tagged_address_word_survives_a_call_framing_its_neighbour.c";

spec enum Identity { At(struct node*) }

resource cell(p: struct node*) {
    field model: Identity;
    match model {
        Identity::At(identity) => {
            owns p->tag;
            owns p->count;
            fact p == identity;
        },
    }
}

void set_count(struct node *p) {
    owns p->count;
    ensures p->count == 1;
}

void tag_then_count(struct node *p) {
    consumes c: cell(p);
    ensures 1 == 1;
} by {
    step_until(loop(0));
    loop {
        owns c: cell(p);
        decreases 0;
        initialize by solve();
        preserve by {
            match c.model {
                Identity::At(identity) => {
                    unfold(c);
                    step();
                    have identity->tag == (address(identity) | 1) by {
                        solve() using { p->tag == (address(p) | 1); p == identity; };
                    }
                    have separate(memory(p->count), memory(p->tag)) by { solve(); }
                    have contains(memory(p->tag), memory(p->tag)) by { normalize(); }
                    mark before_call;
                    step(set_count, {});
                    have separate(statement(0).statement(1).footprint, memory(p->tag)) by {
                        apply(click::separation::separate_restrict(memory(p->count), memory(p->tag), statement(0).statement(1).footprint, memory(p->tag))) using {
                            separate(memory(p->count), memory(p->tag));
                            contains(memory(p->count), statement(0).statement(1).footprint);
                            contains(memory(p->tag), memory(p->tag));
                        };
                    }
                    have p->tag == at(before_call, p->tag) by {
                        preserve(memory(p->tag), statement(0).statement(1));
                    }
                    have identity->tag == (address(identity) | 1) by {
                        rewrite(identity, p);
                        rewrite(p->tag, at(before_call, p->tag));
                        known();
                    }
                    step();
                },
            }
        }
    }
}
```

```expect
pass
```
