# An `extract` refusal prints plain parameters as `<unnamed A>`

Soundness: not soundness. The refusal is correct; its message names the
wrong thing.

## Violated invariant

A diagnostic names the construct the user wrote (CLAUDE.md: a diagnostic
must not name the wrong construct). When `extract(P)` is refused because `P`
is not a proper conjunct of a known fact, the message should print `P` in
source syntax. For `extract(m != i)`, where `m` and `i` are plain `int32`
parameters and `m != i` is a whole `requires` fact, the message instead
prints the proposition with source-policy placeholders:

```
`extract` proposition is not a proper conjunct, a checked disjunction
projection, a discharged implication consequent, or a field equality of an
exact same-constructor equality
<unnamed A> != <unnamed B>
```

The same text appears at the execution frontier, after execution, and in a
`have` body, so the cause is the rendering of the extracted proposition
(`src/surface/proof/proof_object/fixed_state_steps.rs`, the refusal near
"is not a proper conjunct"), not the proof context. The source printer
(`src/surface/proof_diagnostics/render/surface.rs`) falls back to
`<unnamed A>` when a term has no source name, so the extracted proposition
reaches it without its parameter names, although the source spelling the
user wrote is at hand.

## Reproduction

```c filename=f.c
void mark_one(int32 a[], int32 n, int32 i, int32 m) {
    a[i] = 1;
}
```

```click
verifying "f.c";

void mark_one(int32 a[], int32 n, int32 i, int32 m) {
    requires 0 <= i;
    requires i < n;
    requires 0 <= m;
    requires m < n;
    requires m != i;
    requires n <= 1073741823;
    owns a[0..n];
    ensures a[m] == old(a[m]);
} by {
    mark entry;
    step();
    have m != i by {
        extract(m != i);
    }
    execute();
    simp();
}
```

Observed on `master` at `00d053a34`: the refusal above, ending in
`<unnamed A> != <unnamed B>`.

## Intended regression

An mdtest with the program above that expects the refusal to name
`m != i`, for example `fail: ... m != i`.

## Acceptance criteria

- The `extract` refusal prints the extracted proposition as written
  (`m != i`).
- A proposition with operands that truly have no source name still uses the
  documented placeholders.
- The mdtest above is in the gate.
