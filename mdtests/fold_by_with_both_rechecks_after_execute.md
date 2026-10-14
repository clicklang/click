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
import click::machine_integer;
resource holder_of(h: struct holder*) {
    owns *h;
    let cell: int32* where h->target == cell and 0 <= h->count;
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
            extract(at(function.entry, 0) <= at(function.entry, h->count));
            extract(h->target == p);
            apply(int32_increment_lower_bound(at(function.entry, h->count), at(function.entry, 0), at(function.entry, 100))) using {
                at(function.entry, 0) <= at(function.entry, h->count);
                at(function.entry, h->count < 100);
            }
        }
    }
    assumption();
}
```

```expect
pass
```
