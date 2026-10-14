# `let { witness: name } = unfold(r)` names a witness a later fold spells

`holder_of`'s body binds the witness `cell`. Naming it at the unfold gives the
proof a name for its value, so when the increment leaves the fold's body fact
`h->target == cell and 0 <= h->count` unstated, the fold spells that fact with
`p` and the implicit `auto` proves it. Without the name the witness has no
source spelling and the fold falls back to the counted search.

```c filename=unfold_names_a_witness_for_a_fold_body_fact.c
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
    let cell: int32* where h->target == cell and 0 <= h->count;
}

verifying "unfold_names_a_witness_for_a_fold_body_fact.c";

void bump(struct holder* h) {
    requires h != 0;
    requires h->count < 100;
    owns holder_of(h);
} by {
    let { cell: p } = unfold(holder_of(h));
    execute();
    fold(holder_of(h));
    simp();
}
```

```expect
pass
```
