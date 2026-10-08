# Specification pointer loads at equal addresses

No C read or write is needed to state this congruence: the same pointer cell,
in the same state, has the same value through equal base pointers. Ownership
of the cell is explicit.

```c filename=specification_pointer_load_alias.c
struct node { struct node *next; };
void check(struct node *p, struct node *q) {}
```

```click
verifying "specification_pointer_load_alias.c";

void check(struct node* p, struct node* q) {
    owns p->next;
    requires p != 0;
    requires p == q;
    ensures p->next == q->next;
} by {
    have p == q by { assumption(); }
    have &p->next == &q->next by { simp(); }
    have p->next == q->next by { simp(); }
    execute();
    simp();
}
```

```expect
pass
```
