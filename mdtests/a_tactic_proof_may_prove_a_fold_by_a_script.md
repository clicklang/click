# a tactic's proof may prove a fold's facts with a script

A tactic's proof runs no C, so it may not `step`. A `fold` that proves the
facts of the instance it folds with `by { ... }`, as in
`let y = fold(cell_at(p), { value: x.value }) by { close(); }`, runs no C
either: the script proves facts at the fold's point. The tactic is accepted.
Expansion writes this form for a smart `fold`, so expanding a tactic that
folds produces it.

```c filename=a_tactic_proof_may_prove_a_fold_by_a_script.c
void user(int *p) {
}
```

```click
verifying "a_tactic_proof_may_prove_a_fold_by_a_script.c";

resource cell_at(p: int32*) {
    field value: int32;
    owns *p;
    fact *p == value;
}

resource cell2_at(p: int32*) {
    field value: int32;
    owns *p;
    fact *p == value;
}

tactic convert(p: int32*) {
    consumes x: cell_at(p);
    produces y: cell2_at(p);
    ensures y.value == old(x.value);
} by {
    unfold(x);
    let y = fold(cell2_at(p), { value: old(x.value) }) by {
        close();
    }
    have y.value == old(x.value) by { close(); }
}

void user(int32* p) {
    consumes a: cell_at(p);
    produces b: cell2_at(p);
} by {
    let { y: b } = convert(p, { x: a });
    step_until(function.exit);
    close();
}
```

```expect
pass
```
