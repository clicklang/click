# A static ordinary return refold is not retained before a named fold

Soundness: incomplete. A function that preserves one owned cell and creates a
field-only ghost resource is refused after refolding the cell's ordinary
wrapper. No false acceptance is known.

The guarded/iterated return refold and scope-close fixes do not cover an
ordinary wrapper containing only a static owned range. Reproduce with this
mdtest body (the C function is `void inspect(int32* p) { }`):

```click
verifying "refold.c";
resource cell(p: int32*) { owns p[0..1]; }
resource marker() { field value: int32; }
void inspect(int32* p) {
    owns cell(p);
    produces tag: marker();
    ensures tag.value == 1;
} by {
    unfold(cell(p)); execute(); fold(cell(p));
    let tag = fold(marker(), { value: 1 });
    simp();
}
```

The named fold fails with `return observation has a different published state`.
The ordinary macro fold uses the final contract-definition law without updating
the retained return observation frontier. Named folds require that frontier.

Acceptance: retain a kernel-checked presentation for this ordinary fold, make
this reproduction pass, and preserve existing ordinary macro return proofs and
negative checks for extra facts, ownership, and altered snapshots. The solution
must follow the selected resource delta without scanning unrelated state.
