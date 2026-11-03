# A call retains its abstract resource bound without unfolding recursive cells

```c filename=footprint.c
struct node { struct node *next; };
void touch(struct node *child, struct node *other) {}
void caller(struct node *child, struct node *other, int *slot) { touch(child, other); }
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
void touch(struct node* child, struct node* other) { owns list(child); owns list(other); }
void caller(struct node* child, struct node* other, int32* slot) {
    owns list(child);
    owns list(other);
    owns *slot;
} by {
    have separate(list(child), memory(*slot)) by { assumption(); }
    have separate(list(other), memory(*slot)) by { assumption(); }
    apply(separation::separate_star(list(child), list(other), memory(*slot))) using {
        separate(list(child), memory(*slot)); separate(list(other), memory(*slot));
    };
    mark before_call;
    step();
    have contains(list(child) * list(other), statement(0).footprint) by { assumption(); }
    apply(separation::contains_refl(memory(*slot))) using {};
    apply(separation::restrict(list(child) * list(other), memory(*slot), statement(0).footprint, memory(*slot))) using {
        separate(list(child) * list(other), memory(*slot));
        contains(list(child) * list(other), statement(0).footprint);
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
