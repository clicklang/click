# `first` may not claim a head of an unconstrained list

A small list form of the nonempty guard that
[`rb_first_last.md`](rb_first_last.md)'s in-order clause carries. `first` returns
null for a null `head` and `head` otherwise, and its contract claims, with no
guard, that the result starts the modeled list. Nothing ties the model to the
C pointer, and on the null path the claim would need a null head in an
arbitrary list, so the clause must be refused. `simp()` unfolds
`starts_with` into its `match` and tries the path's pointer equality inside it
before giving up. This catches a pointer rewrite through a match body with
bindings that it cannot carry, or a contract lowering of that body that turns
the refusal into an acceptance or a crash.

```c filename=first_rejects_an_unguarded_list_head.c
#define NULL 0

struct node {
    struct node *next;
};

struct node *first(struct node *head) {
    if (!head)
        return NULL;
    return head;
}
```

```click
verifying "first_rejects_an_unguarded_list_head.c";

function starts_with(xs: List<struct node*>, value: struct node*) -> int32 {
    match xs {
        List::Nil => 0,
        List::Cons(head, tail) => if value == head { 1 } else { 0 },
    }
}

resource listed() {
    field model: List<struct node*>;
}

struct node* first(struct node* head) {
    owns l: listed();
    ensures l.model == old(l.model);
    ensures starts_with(old(l.model), result) == 1;
} by {
    execute();
    simp();
}
```

```expect
fail: `ensures starts_with(old(l.model), result) == 1` failed
```
