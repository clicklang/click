# A consumed field-bearing instance bounds the call footprint at a mark

A call that consumes a resource instance with fields bounds its footprint by that instance. After the call the state no longer holds it, so the proof names it as `at(before_call, b)`.

```c filename=consuming.c
struct node { struct node *next; };
void touch(struct node *child) {}
void caller(struct node *child, int *slot) { touch(child); }
```

```click
import click::separation;
verifying "consuming.c";
resource box(p: struct node*) {
    field tag: int32;
    owns p->next;
}
void touch(struct node* child) {
    consumes b: box(child);
    produces c: box(child);
} by {
    unfold(b);
    let c = fold(box(child), { tag: 0 });
}
void caller(struct node* child, int32* slot) {
    consumes b: box(child);
    owns *slot;
    produces c: box(child);
} by {
    have separate(b, memory(*slot)) by { assumption(); }
    mark before_call;
    let { c: c } = step(touch, { b: b });
    have contains(at(before_call, b), statement(0).footprint) by { assumption(); }
    apply(separation::contains_refl(memory(*slot))) using {};
    apply(separation::restrict(at(before_call, b), memory(*slot), statement(0).footprint, memory(*slot))) using {
        at(before_call, separate(b, memory(*slot)));
        contains(at(before_call, b), statement(0).footprint);
        contains(memory(*slot), memory(*slot));
    };
    have *slot == at(before_call, *slot) by {
        transport_certificate {
            premise 0: separate(statement(0).footprint, memory(*slot)) => separate(statement(0).footprint, memory(*slot));
            preserve 0 => *slot == at(before_call, *slot);
            conclusion 1;
        }
    }
}
```

```expect
pass
```
