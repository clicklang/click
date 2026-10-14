# Retained resource lookup omits checked framed pointer carriers

Soundness: incomplete. The archived object-model implementation rejects a
supported C loop proof when the surface rewrite and retained kernel checker
use different candidate-discovery paths. No false acceptance is demonstrated.

Priority: P2. Branch regression blocking the affected activation.

## Reproduction and evidence

The following complete reduction passes fresh, expanded-source and retained
checking on the entry-fold repair delivered in PR #937. After the loop escape
repair at `6b8c5a1bb`, the archive rejects its `unfold` with
`the rewritten composite is absent from both resource representations`.

# A loop resource can select its backing through a framed descriptor field
```c filename=probe.c
struct holder { int32* data; };
void probe(struct holder* h, int32 n) {
    int32 i = 0;
    while (i < n) { h->data[i] = 1; i++; }
}
```
```click
verifying "probe.c";
resource cells(data: int32*, n: int32) { owns data[0..n]; }
void probe(struct holder* h, int32 n) {
    requires 0 <= n;
    requires n <= 536870911;
    views h->data;
    owns cells(h->data, n);
} by {
    step(); step();
    loop {
        owns cells(h->data, n);
        decreases n - i;
        invariant 0 <= i;
        invariant i <= n;
        initialize by simp;
        preserve by {
            unfold(cells(h->data, n));
            step(); step();
            fold(cells(h->data, n));
            close_invariants();
        }
    }
    execute(); simp();
}
```
```expect
pass
```

A bounded local probe compares the two existing lookup paths. The broad
same-family check reports both arguments equal (`[true, true]`); the narrowed
pointer-root index reports zero candidates. The surface's incremental consumption
uses the broader family index and consumes the actual held head. The retained
kernel check cannot rediscover that head through its pointer-root index.

The selected complete-cell frame relation already canonicalizes the two pointer
carriers to the same immutable read. Candidate discovery must cover that relation
without scanning unrelated resource holdings. A candidate index is not proof:
argument equality, pointer origin and ownership quantity still need their existing
checks. Numeric address equality must not create a typed-place witness.

Correcting discovery exposes a second disagreement: the surface unfolds the
written selector again while the retained kernel expands the selected resource's
stored arguments. They produce equivalent but differently spelled memory facts,
and the kernel rejects an unchecked pure-fact delta. Expand the selected C-value
arguments consistently in both paths; retain existing handling of non-C indices.

## Acceptance

- Verify the reduction fresh, expand and verify its rewritten proof, and recheck
  a retained session; do not change its C or claims.
- Keep candidate lookup bounded by selected read/frame evidence and indexed
  related holdings. Include deterministic multi-size coverage beside unrelated
  loaded-pointer resources and a withdrawal control for index maintenance.
- Reject changed or partially written pointer cells, including under asserted
  numeric address equality, and retain strict-native/explicit-validity controls.
- Recheck the original normal example stage. Report later failures separately
  from the reduced rewrite repair; retain all existing work budgets.

## Preserved recovery candidate

The recovery tree now indexes producer read identities as well as pointer roots,
including unconditional checked frame canonicalization at publication. Queries
also use their own checked frame evidence, then run the unchanged argument and
quantity checks. Removing a resource removes its read-index entries. The surface
uses the selected C-value arguments when expanding an unfold; non-C indices keep
their existing handling.

All 31 selected pointer-designation, native-span and loop-carrier kernel tests
pass. The new regression bounds query work below 100 units beside 16, 64, 256
and 1,024 unrelated loaded-pointer resources, checks withdrawal, and rejects
partial writes even under numeric address equality. Both C++ member-domain
rejection fixtures pass. Eight of nine selected resource-unfold Markdown fixtures
pass; the ninth (`resource_unfold_names_unmatched_body_cells`) fails with the
same pointer-arithmetic error on the earlier `6b8c5a1bb` checkpoint. The archived
fieldless entry-fold fixture also retains its preexisting rejection; upstream
PR #937 already repairs that independent bug.

The full normal example stage checks the same 52 projects: 39 pass and 13 fail
in 137.45s, with no new failing project relative to `86abef177`. Fork/join passes
all four proof modes; an escape-only `6b8c5a1bb` executable already passes that
original project, so its restoration is credited to the earlier member-escape
repair, not this index candidate.

The original reduction now passes the retained `unfold`, but fails later at its
post-store `fold(cells(h->data, n))`. Arena still exhausts its unchanged control
budget. This is not a green activation or a complete repair of the reduction.

A follow-up safeguard retains each entry's publication-time read-index keys
for withdrawal instead of recomputing them after late producer frame edges.
The multi-size lookup regression and a dedicated late-edge withdrawal test both
pass on this follow-up. The 39/52 example-stage verdict above is for the initial
candidate; no additional full stage is claimed for the withdrawal-only change.

## Follow-on backing-range discovery reduction

On preserved recovery checkpoint `bcb416098`, the original loop above reaches
its post-store fold but still rejects `owns h->data[0..n]`. A focused trace
records the held backing range at the descriptor's initial pointer read and
shows the backing write before the failed fold. The normal diagnostic prints
the held and requested ranges identically; that spelling does not establish
that their internal snapshot reads are identical.

A temporary, bounded investigation probe at incremental memory consumption
reports **zero indexed candidates**. Checking the three held memory facts with
the unchanged `resource_fact_entails` comparator reports false for the descriptor
view and local counter owner, and **true for the backing owner**. Its bounds and
stride match the request (`0..n`, four bytes); its pointer-read variable differs.
The cheap `pointers_known_equal` query reports false for the backing pair,
although ordinary resource coverage accepts it. This isolates candidate
discovery as insufficient for a relation already accepted by coverage; it does
not justify admitting a new equality or typed-place rule.

The probe inspects only this reduced context and is removed from production.
Do not turn that diagnostic scan into a lookup fallback. A repair must select
suppliers through indexed, checked producer/frame evidence, retain the final
coverage check, and include authority-withdrawal and partial-pointer-write
rejection controls plus deterministic scaling beside unrelated holdings.

Replacing the backing write with a write through an independently owned `aux`
pointer retains the same miss: zero candidates, but accepted backing coverage.
The symptom therefore does not require modifying the backing buffer itself.

After removing the probe and rebuilding the unchanged recovery checkpoint,
the original loop still fails at that fold. The counter-only loop and the
non-loop descriptor unfold/fold round trip both pass fresh checking, expansion,
verification of the rewritten proof and retained-session rechecking. These
controls bound the reduction; they are not a repaired original loop.

## Checked endpoint repair

The memory-query repair resolves only the selected producer read through at
most 64 existing cell-history hops, checks every retained hop under live facts,
and adds the resulting address equality only to that query's cloned graph.
The supplier still needs the ordinary ownership and coverage checks. Only a
certified supplying write yields a stored pointer value. If the walk stops at
an unproved/affecting edge, its endpoint is the opaque read at that snapshot;
the snapshot's cached old cell cannot justify transport across the edge.

The frame witness also exposes a signed-order certificate mismatch: the
producer can prove `1 < n` from a path beginning with `2 <= n`, while the checker
previously allowed an intrinsic constant connection only at the path's end.
Check forward constant connections at the start and between retained steps as
well, carrying their strictness and still checking every recorded premise.
Reversed connections, unsupported symbolic gaps, missing strictness and withdrawn
premises must reject.

The deterministic lookup regression selects one owner beside 16, 64, 256 and
1,024 unrelated loaded-pointer ranges with work below 2,000 at every size.
It checks consumption, removal of the selected owner, withdrawal of frame
separation, partial pointer-cell writes and isolation of the caller's graph.
The original C and proof are preserved in
[`loop_resource_backing_range_fold_after_write.md`](../mdtests/loop_resource_backing_range_fold_after_write.md).

The final safe recovery candidate passes all 84 selected memory-index,
pointer-designation, native-span and loop-carrier controls, but the original
archive loop still rejects its post-store fold. An earlier local prototype
passed that loop by taking a cached pointer value at an unproved stopping write;
the withdrawal control rejects that approach, and it is removed. Do not credit
that apparent success. The master extraction passes all 59 selected memory-index
and order-certificate controls, the original loop and both existing partial-write
fixtures. Its loop passes fresh, expansion, rewritten and retained checks.
The remaining archive read-chain gap still needs attribution; no new full
example-stage or activation verdict is claimed.
