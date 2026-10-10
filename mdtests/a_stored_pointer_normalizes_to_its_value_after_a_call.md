# a stored pointer normalizes to its value after a call

`link` stores `p` into `q->left` and then calls a function that changes
only `p->tag`. After the call, `normalize()` with an empty `using` list
proves `q->left == p`: the current read of the link names the same unchanged
cell as the recorded store, so the pointer equality bridges through the load's
origin without any listed premise. This catches pointer-offset origin
bridging that loses a stored pointer value across a framed call.

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
} by { execute(); simp(); }
void link(struct node *p, struct node *q) {
    owns p->tag; owns q->left;
    ensures q->left == p;
} by {
    step();
    step(touch(p), {});
    have q->left == p by { normalize() using { } }
    execute(); simp();
}
```

```expect
pass
```
