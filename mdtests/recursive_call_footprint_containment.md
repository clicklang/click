# A call retains its abstract resource bound without unfolding recursive cells

```c filename=footprint.c
struct node { struct node *next; };
void touch(struct node *child) {}
void caller(struct node *child, int *slot) { touch(child); }
```

```click
import click::separation;
verifying "footprint.c";
resource list(p: struct node*) {
    if p != 0 {
        owns p->next;
        owns list(p->next);
    }
}
void touch(struct node* child) { owns list(child); }
void caller(struct node* child, int32* slot) {
    owns list(child);
    owns *slot;
} by {
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
