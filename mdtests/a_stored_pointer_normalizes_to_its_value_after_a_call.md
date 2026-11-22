# A stored pointer retains its value after a call

`link` stores `p` into `q->left` and then calls a function that changes only
`p->tag`. After the call, `known()` checks that the current link read has the
recorded value `p`. The fixture checks that the verifier retains the stored
pointer across the call.

```c filename=a_stored_pointer_normalizes_to_its_value_after_a_call.c
struct node { uint64 tag; struct node *left; };
void touch(struct node *p) { p->tag = 1; }
void link(struct node *p, struct node *q) { q->left = p; touch(p); }
```

```click
verifying "a_stored_pointer_normalizes_to_its_value_after_a_call.c";
void touch(struct node *p) {
    owns p->tag;
    ensures p->tag == 1;
}
void link(struct node *p, struct node *q) {
    owns p->tag; owns q->left;
    ensures q->left == p;
} by {
    step();
    step(touch);
    have q->left == p by { known(); }
}
```

```expect
pass
```
