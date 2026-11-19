# a fold's `by` body with `all positional` checks after the C runs

This is the expansion of
`mdtests/unfold_names_a_witness_for_a_fold_body_fact.md`: the implicit
closer proved the fold's open body fact with `all positional`. Checked again as
written, each arm of the `all positional` is checked as its own script.

```c filename=fold_by_with_both_rechecks_after_execute.c
struct holder {
    int32 count;
    int32* target;
};

void bump(struct holder* h) {
    h->count = h->count + 1;
}
```

```click
resource holder_of(h: struct holder*) {
    owns *h;
    let cell: int32* where h->target == cell and (h->count < 200 or cell == 0);
}

verifying "fold_by_with_both_rechecks_after_execute.c";

void bump(struct holder* h) {
    requires h != 0;
    requires h->count < 100;
    owns holder_of(h);
} by {
    let { cell: p } = unfold(holder_of(h));
    step();
    step();
    fold(holder_of(h)) by {
        all positional {
            left => {
                known();
            }
            right => {
                have h->count < 200 by {
                    solve() using { at(function.entry, h->count < 100); };
                }
                known();
            }
        }
    }
    known();
}
```

```expect
pass
```
