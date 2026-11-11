# A call that consumes a recursive resource bounds its footprint by it

A resource-derived call writes only memory the caller hands it. When it consumes a recursive resource and produces another, the call still publishes `contains(input, footprint)`, so a cell the caller kept is carried across the call through `separation::restrict` and `preserve`.

```c filename=consuming.c
struct node { struct node *next; };
void touch(struct node *child) {}
void caller(struct node *child, int *slot) { touch(child); }
```

```click
import click::separation;
verifying "consuming.c";
resource list(p: struct node*) { if p != 0 { owns p->next; owns list(p->next); } }
resource relist(p: struct node*) { owns list(p); }
void touch(struct node* child) { consumes list(child); produces relist(child); } by { fold(relist(child)); }
void caller(struct node* child, int32* slot) { consumes list(child); owns *slot; produces relist(child); } by {
    have separate(list(child), memory(*slot)) by { assumption(); }
    mark before_call;
    step();
    have contains(list(child), statement(0).footprint) by { assumption(); }
    apply(separation::contains_refl(memory(*slot))) using {};
    apply(separation::restrict(list(child), memory(*slot), statement(0).footprint, memory(*slot))) using {
        separate(list(child), memory(*slot));
        contains(list(child), statement(0).footprint);
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
