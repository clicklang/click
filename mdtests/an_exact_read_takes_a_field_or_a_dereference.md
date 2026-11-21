# An exact read takes a field or a dereference

`exact` takes any place whose ordinary read is legal (`design/exact-reads.md`):
a pointer field `h->next`, a dereference `*q`, and a field read through an
exact pointer read, `exact(exact(h->next)->next)`, where the inner `exact`
names the address read too. After the store to `*q`, `h->next` is unchanged,
so its exact read equals its ordinary read; the stored `*q` is 1 however it
is named.

```c filename=an_exact_read_takes_a_field_or_a_dereference.c
struct node { struct node *next; };
void touch(struct node *h, int *q) { *q = 1; }
```

```click
verifying "an_exact_read_takes_a_field_or_a_dereference.c";
void touch(struct node* h, int32* q) {
    owns h->next;
    owns *q;
    ensures *q == 1;
} by {
    step_until(function.exit);
    have exact(h->next) == h->next by known();
    have exact(*q) == 1 by known();
    have exact(*q) == *q by known();
    have exact(exact(h->next)->next) == h->next->next by solve();
}
```

```expect
pass
```
