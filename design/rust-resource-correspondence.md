# Rust ownership and Click resources: worked correspondence

This record tests whether ordinary safe Rust ownership and borrowing can map
naturally to Click resources. It pairs compiler/runtime witnesses in
`design/borrow-probes/resource_correspondence.rs` with the
`rust_correspondence_` tests in `src/kernel/tests/loan_model_tests.rs`.
The witnesses are synthetic and unchanged between compiler and model analysis.
Click does not yet import or verify their Rust source.

## Proposed interpretation

| Rust operation | Resource interpretation | Boundary |
| --- | --- | --- |
| Own a non-`Copy` value | Hold its contents and management authority | Memory access, allocation lifetime, and type validity remain distinct. |
| Move that value | Transfer its resources; the former holder loses access | Moving a value need not preserve its physical address. Model contexts represent authority holders, not Rust threads. |
| Borrow `&mut T` | Lend exclusive access, retaining the lender's recovery right | Exclusive access does not itself grant deallocation or ownership of the allocation. |
| Borrow ordinary `&T` | Lend stable shared access | This interpretation excludes interior-mutability payloads. |
| Reborrow | Restrict the parent for the borrowed footprint | Different disjoint fields may retain independent access. |
| Finish using a borrow | Recover authority with the updated contents | Recovery cannot duplicate authority or revive an expired child. |

An `owns` clause at a Click function boundary borrows and returns the selected
resource. For ordinary memory this closely matches an `&mut` parameter's
exclusive access. It does not mean that the callee receives a Rust owned
value or permission to free the allocation. A move instead matches a
consumed input and, where appropriate, a produced output. A `views` clause
matches ordinary shared access backed by suspended exclusive authority.
Rust types can supply these access requirements implicitly in a future
frontend; users need not restate every compiler-established restriction.

## Worked traces

### Owned value and move

`move_transfers_noncopy_value` moves a plain `Pair` to a recipient and changes
its left field from 4 to 8, preserving right = 9. The rejection witness
`use_after_move` attempts to read the former owner's field afterward.

`rust_correspondence_move_transfers_authority_without_copying_it` models the
same authority transfer using a concrete range. The former holder can neither
write nor transfer it again. While the recipient lends a shared borrow,
transfer and early recovery are refused. Closing the borrow restores authority
exactly once; the stale shared handle cannot read afterward.

The range model deliberately omits physical relocation, destructors, and
allocation validity. Its transfer is evidence for linear authority, not an
implementation of Rust move execution. Its bytes initially all contain 4;
the Rust struct's separate field values are not modeled in this trace.

### Shared field borrow

`shared_borrow_preserves_field_until_parent_reuse` starts with left = 4 and
right = 9. A shared borrow protects left while the parent changes right to 12.
After the last shared read, the parent changes left to 8. The final pair is
(8, 12). The rejection witness `write_during_shared` instead writes left
before the shared reference's last use.

`rust_correspondence_shared_field_preserves_value_and_allows_disjoint_write`
checks that same value trace. A write through either the parent to the
borrowed field or the shared child is refused. The unrelated field remains
writable. After child closure, the parent can write the borrowed field.

Production Click already supports stable shared lending, shared reborrows,
and partial-range access. The existing
`correspondence_calls_production_shared_reborrow_and_end_ordering` test
exercises the production ledger directly; `mdtests/stable_view_partial_borrow.md`
checks a source-level C partial borrow. The new field trace is an independent
model test, not a new production Rust operation.

### Exclusive field reborrow and recovery

`exclusive_reborrow_returns_updated_field_and_preserves_neighbor` passes
left to a helper. Inside the helper a child mutable reference writes 7;
its parent then increments that value to 8. Back in the caller, right remains
9 and a later parent write changes left to 10. The child variable's local
storage need not end before parent reuse. The rejection witness
`parent_during_child` keeps the child in use after a conflicting parent write.

`rust_correspondence_exclusive_reborrow_recovers_updated_value_once` checks
the helper's 4 -> 7 -> 8 trace and preservation of right = 9. Parent reads,
parent writes, and another child borrow are refused while the exclusive
child is active. Forged child identities and holders cannot recover it or
alter the outstanding state. Closing it returns 7, after which the parent
can write 8. Stale child reads, writes, and duplicate recovery are refused.
The final-value comparison also distinguishes the actual 8 from the false
claim 7. This is a concrete model assertion, not rejection of a submitted
Rust proof or a universal functional-correctness theorem.

Exclusive reborrowing and value transport here are model-only. The production
ledger has no corresponding exclusive-reborrow API. The field model also
conservatively suspends *all* parent access for an exclusive child and admits
only one child at a time; that is stricter than Rust's field-sensitive rules.
It must not become the acceptance rule for a Rust frontend unchanged.

### Disjoint exclusive fields

`disjoint_exclusive_fields_can_be_used_together` holds mutable references to
both fields at once, writes (8, 12), and then reads the whole pair.
`rust_correspondence_partition_supports_disjoint_exclusive_access` partitions
one range into two independently held ranges, checks writes to each, and
returns and rejoins their authority. Whole-parent access and access through
the wrong field holder are refused until the ranges return.

This demonstrates the necessary resource partition. It does not yet combine
partitioning with the exclusive child dependency model, nested reborrows,
or implicit borrow-end discovery. Those connections remain implementation
work; the smaller field model's conservative restriction is not evidence that
Rust forbids disjoint mutable borrows.

## Compiler and proof responsibilities

The recommended first frontend trusts pinned rustc type and borrow checking
for accepted safe Rust, including move legality and legal parent reuse.
Click need not independently reconstruct Rust's borrow checker. It must still
translate mutations, calls, and contracts soundly and relate the updated
borrowed contents to the lender's contents. Ghost/sidecar access must not
introduce conflicting usable authority that rustc never checked.

The explicit `end_child` in these traces describes resource accounting; it
does not prescribe a source annotation or require extracting every inferred
lifetime. An importer may use compiler borrow information, an explicit-memory
interpretation, or a value-based interpretation with resolution rules. Choose
that boundary after comparing typed HIR and MIR on these witnesses.

Verus is a useful architectural reference: its main translation uses typed
HIR into a verification IR, uses Rust lifetime checking, and gives mutable
references initial/final values with a resolution analysis. Those are options
to study, rather than grounds for assuming MIR or a complete loan export is
mandatory. See its [architecture](https://github.com/verus-lang/verus/blob/main/source/CODE.md),
[borrowing guide](https://verus-lang.github.io/verus/guide/mutation-references-borrowing.html),
and [mutable-reference guide](https://verus-lang.github.io/verus/guide/mutable-references.html).

Interior mutability needs a type-specific sharing protocol. `&Cell<T>` cannot
map to a stable read-only view of its payload; `&Mutex<T>` grants operations
that temporarily acquire payload authority. Unsafe Rust, allocation provenance,
returned references, destructors, panics, and general type validity are outside
this worked correspondence. Overflow in the helper is impossible after the
constant write of 7, but there is no general arithmetic or panic policy here.

## Reproduction and acceptance

Use the repository's pinned toolchain (`rustc 1.98.1` for this record):

```console
rustc --edition=2024 --test design/borrow-probes/resource_correspondence.rs -o /tmp/click-resource-correspondence
/tmp/click-resource-correspondence
cargo nextest run --lib -E 'test(rust_correspondence_)'
cargo nextest run --lib -E 'test(correspondence_calls_production_)'
```

Compile each negative separately. Every command below must fail, with E0506,
E0506, and E0382 respectively; a successful compile fails the investigation.

```console
rustc --edition=2024 --cfg parent_during_child design/borrow-probes/resource_correspondence_rejected.rs -o /tmp/click-resource-rejected
rustc --edition=2024 --cfg write_during_shared design/borrow-probes/resource_correspondence_rejected.rs -o /tmp/click-resource-rejected
rustc --edition=2024 --cfg use_after_move design/borrow-probes/resource_correspondence_rejected.rs -o /tmp/click-resource-rejected
```

Acceptance requires all four Rust runtime tests and all four independent
resource traces to pass, all three compiler rejection cases to fail as
specified, and the existing production correspondence tests to pass. This
supports the resource interpretation for these cases. It does not establish
Rust frontend support, validate an importer, or prove a refinement between
Rust execution and the model.
