# A join keeps a cell both arms agree on

The arms of the `if` store different values to `p->left`, so their memories
differ and the join abstracts them. Neither arm touches `p->right`: both end
holding the same value for it, which is therefore its value after the join.
The read after the join returns what the function was entered with, and no
`ensuring` fact has to restate it.

The store both arms disagree on is still forgotten:
`a_join_forgets_a_cell_the_arms_disagree_on` is the same function claiming
the value of `p->left`.

```c filename=a_join_keeps_a_cell_both_arms_agree_on.c
struct pair { int32 left; int32 right; };

int32 put(struct pair *p, int32 x) {
    if (x <= 0) {
        p->left = 0;
    } else {
        p->left = 1;
    }
    return p->right;
}
```

```click
verifying "a_join_keeps_a_cell_both_arms_agree_on.c";

int32 put(struct pair* p, int32 x) {
    requires p != 0;
    owns p->left;
    owns p->right;
    ensures result == old(p->right);
} by {
    branch ensuring {
        fact 1 == 1;
    } then {
        step();
    } else {
        step();
    }
    step();
    simp();
}
```

```expect
pass
```
