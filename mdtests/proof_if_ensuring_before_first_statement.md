# A proof if interface can precede the first C statement

```c filename=probe.c
struct node { unsigned long tag; struct node *other; struct node *next; };
void probe(struct node *p, struct node *q, struct node *value) {}
```

```click
verifying "probe.c";
void probe(struct node *p, struct node *q, struct node *value) {
    owns p->next;
    requires p->next == value;
    ensures p->next == value;
} by {
    if p == q ensuring {
        owns p->next;
        fact p->next == value;
    } then {
        have p->next == value by assumption();
    } else {
        have p->next == value by assumption();
    }
    execute(); simp();
}
```

```expect
pass
```
