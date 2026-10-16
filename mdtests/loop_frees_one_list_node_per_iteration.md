# a loop may free one node per iteration and continue

The ordinary iterative list release frees the node it unfolded and moves to
the next one. The loop head holds the rest of the list folded inside its
binder, so the node freed in an iteration was never a live allocation the head
recorded: the back edge differs from the head only by that allocation's
tombstone, which is a double-free and stale-pointer diagnostic, not authority.
The binder `x` still has to hold the list that remains, and its model's
length ranks the loop.

```c filename=loop_frees_one_list_node_per_iteration.c
struct node {
    struct node *next;
};

void release(struct node *p) {
    while (p != 0) {
        struct node *next = p->next;
        free(p);
        p = next;
    }
}
```

```click
verifying "loop_frees_one_list_node_per_iteration.c";

spec enum Links { Nil, Cons(Links) }

function links_len(m: Links) -> Integer
    decreases m
{
    match m {
        Links::Nil => 0,
        Links::Cons(rest) => links_len(rest) + 1,
    }
}

theorem links_len_is_nonnegative(m: Links) {
    ensures 0 <= links_len(m) by {
        induct(m) as ih {
            Links::Nil => {
                unfold(links_len(Links::Nil));
                normalize();
            }
            Links::Cons(rest) => {
                apply(ih(rest));
                unfold(links_len(Links::Cons(rest)));
                arithmetic() using { 0 <= links_len(rest); }
            }
        }
    }
}

resource list_at(p: struct node*) {
    field model: Links;
    match model {
        Links::Nil => { fact p == 0; },
        Links::Cons(rest_model) => {
            owns allocation(p, sizeof(struct node));
            owns *p;
            owns rest: list_at(p->next);
            fact p != 0;
            fact rest.model == rest_model;
        },
    }
}

void release(struct node* p) {
    consumes x: list_at(p);
} by {
    loop {
        owns x: list_at(p);
        decreases links_len(x.model);

        initialize by simp();
        preserve by {
            match x.model {
                Links::Nil => { contradiction(x.model == Links::Nil); },
                Links::Cons(rest_model) => {
                    apply(links_len_is_nonnegative(rest_model));
                    have links_len(x.model) == links_len(rest_model) + 1 by {
                        rewrite(x.model == Links::Cons(rest_model));
                        unfold(links_len(Links::Cons(rest_model)));
                        normalize();
                    }
                    have links_len(rest_model) < links_len(x.model) by {
                        arithmetic() using { links_len(x.model) == links_len(rest_model) + 1; }
                    }
                    let { rest: r } = unfold(x);
                    have 0 <= links_len(r.model) by {
                        rewrite(r.model == rest_model);
                        assumption();
                    }
                    step();
                    step();
                    step();
                    step();
                    close_invariants();
                },
            }
        }
    }
    unfold(x);
    step();
    simp();
}
```

```expect
pass
```
