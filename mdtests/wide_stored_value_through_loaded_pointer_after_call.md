# A selected pointer alias recovers a wide stored value after a named call

The C local holds a pointer loaded before the store. A named resource call
clears its cached read; the explicit alias must connect that read to the caller’s
kept ownership and the recorded eight-byte store.

```c filename=flat.c
struct Node { unsigned long tag; struct Node *next; };
void helper(struct Node *p) { p->tag = 0; }
void caller(struct Node *p, struct Node *q) {
    struct Node *r = p->next;
    r->tag = 7;
    helper(p);
}
```

```click
import click::separation;
verifying "flat.c";
spec enum Tag { Here }
resource tag(p: struct Node*) { field model: Tag; owns p->tag; fact model == Tag::Here; }
void helper(struct Node *p) { consumes before: tag(p); produces after: tag(p); }
by { unfold(before); step_until(function.exit); let after = fold(tag(p), {model: Tag::Here}); close(); }
void caller(struct Node *p, struct Node *q) {
    consumes before: tag(p); produces after: tag(p);
    owns p->next; owns q->tag;
    requires p->next == q;
    ensures q->tag == 7;
} by {
    step(); step(); step();
    have r->tag == 7;
    have r == q;
    have q->tag == 7 by {
        rewrite(q, r);
        close();
    }
    have separate(before, memory(q->tag)) by close();
    mark before_call;
    let {after: after} = step(helper, {before: before});
    have contains(at(before_call, before), statement(2).footprint) by close();
    apply(separation::contains_refl(memory(q->tag)));
    apply(separation::separate_restrict(at(before_call, before), memory(q->tag), statement(2).footprint, memory(q->tag)));
    have q->tag == at(before_call, q->tag) by {
        preserve(memory(q->tag), statement(2));
    }
    have r == q;
    have r->tag == 7 by {
        rewrite(r, q);
        rewrite(q->tag, at(before_call, q->tag));
        close();
    }
}
```

```expect
pass
```
