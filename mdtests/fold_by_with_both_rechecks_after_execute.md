# a fold's `by` body with `both` checks after `execute()`

This is the expansion of
`mdtests/unfold_names_a_witness_for_a_fold_body_fact.md`: the implicit
`auto` proved the fold's open body fact with `both`. Checked again as
written, each arm of the `both` is checked as its own script.

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
        both {
            assumption();
        } and {
            have h->count < 200 by {
                arithmetic_certificate signed_int32 {
                    premise 0: at(function.entry, h->count < 100) => at(function.entry, h->count < 100);
                    interval_from_affine 0 (at(function.entry, h->count)) (-2147483648) (99);
                    interval_atom (1) (1) (1);
                    interval_add_bounded 1, 2 (-2147483647) (100);
                    trivial => -99 <= 0;
                    add 0, 4 => (at(function.entry, h->count) + -99) < (at(function.entry, 100) + 0);
                    affine_conclusion 5 3 => h->count < 200;
                    conclusion 6;
                }
            }
            assumption();
        }
    }
    assumption();
}
```

```expect
pass
```
