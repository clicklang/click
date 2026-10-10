# Self links do not establish equality of their nodes

A pointer observation must not prove its own address-alias premise.

```c filename=self-links.c
struct node { struct node *next; };
void connect(struct node *p, struct node *q) { p->next = p; q->next = q; }
```

```click
verifying "self-links.c";
void connect(struct node *p, struct node *q) {
 owns p->next; owns q->next;
 ensures p == q;
} by {
 step(); step();
 have p->next == p;
 have q->next == q;
 have p == q by normalize();
 execute(); simp();
}
```

```expect
fail: `normalize` goal did not normalize to true
```
