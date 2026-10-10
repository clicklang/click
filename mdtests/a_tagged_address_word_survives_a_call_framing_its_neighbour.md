# a tagged address word survives a call framing its neighbour

A function stores a pointer's address with its low bit set into a `uint64`
field, then calls a function that owns only the neighbouring field. A fact
about the word recorded before the call, named through the resource model's
identity rather than the C parameter, still holds after the call: the load is
transported to the memory after the call through the wide bitwise-or. This
catches frame transport that gives up on, or wrongly rewrites, a stored
`uint64` or of a pointer address.

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
} by { execute(); simp(); }

void tag_then_count(struct node *p) {
    consumes c: cell(p);
    ensures 1 == 1;
} by {
    execute_until(loop(0));
    loop {
        owns c: cell(p);
        decreases 0;
        initialize by simp;
        preserve by {
            match c.model {
                Identity::At(identity) => {
                    unfold(c);
                    step();
                    have identity->tag == (address(identity) | 1) by {
                        simp() using { p->tag == (address(p) | 1); p == identity; }
                    }
                    mark before_call;
                    step(set_count(p), {});
                    have identity->tag == (address(identity) | 1) by {
                        normalize() using {
                            at(before_call, identity->tag == (address(identity) | 1));
                            p == identity;
                        }
                    }
                    step();
                },
            }
        }
    }
    execute(); simp();
}
```

```expect
pass
```
