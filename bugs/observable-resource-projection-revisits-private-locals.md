# Observable resource projection revisits every private local

## Violated invariant

A simple statement check must not reconstruct unrelated resource state.
`ResourceContext::observable_facts_assuming_valid` clones a shared context,
then walks every automatic owner and removes every never-address-taken local
from the scratch copy. Each removal updates the fact store, support indexes,
resource indexes, and history. Callers in `checked_drivers/statement_step.rs`
and `fixed_state_proofs/theorem_application.rs` repeat this work.

The initial clone is cheap; reconstructing and destroying the filtered
composition is not. Adding an unrelated private scalar changes the source
context but leaves its observable composition unchanged. Repeated projection
still pays for all such scalars. Projection after each declaration is quadratic
in the number of private locals.

The preliminary memory-family scan is also unnecessary today:
`MemoryResourceAlgebra::observable_facts` returns an empty vector and ignores
its input. The current projection is independent of its assumptions argument;
subsequent reasoning about the composition still uses the checked assumptions.

## Reproduction

On commit `c34b8757c0dbd17bdff259cc6b6a2dfda90d1064`, append the following
probe to `src/kernel/tests/resource_scaling_tests.rs`, where its existing
`owned_range` and `heap_base` helpers are available, and run:

```console
cargo test --lib investigate_observable_context_rebuild_cost -- --nocapture
```

The two observable heap owners remain fixed. Hidden locals accumulate in the
source context, and every projected result equals the original observable view.
The counts are deterministic work units, not wall-clock thresholds.

| Private locals | One query | 16 unchanged queries | Insert-and-project sequence |
| ---: | ---: | ---: | ---: |
| 4 | 12 | 192 | 34 |
| 16 | 48 | 768 | 424 |
| 64 | 192 | 3,072 | 6,304 |
| 256 | 768 | 12,288 | 98,944 |

```rust
#[test]
fn investigate_observable_context_rebuild_cost() {
    for size in [4, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        crate::kernel::set_never_address_taken_locals(
            (0..size).map(|index| format!("hidden_{index}")).collect(),
        );
        let assumptions = PureFactContext::new();
        let base = ResourceContext::new().unchecked_with_facts([
            owned_range(heap_base(1), 0, 4),
            owned_range(heap_base(2), 0, 4),
        ]);
        let expected = base.observable_facts_assuming_valid(&assumptions);
        let mut resources = base;
        let (_, sequence_work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 0..size {
                resources = resources.clone().unchecked_with_fact(CResourceFact::own_memory(
                    CMemoryRange::new(CMemory::local_pointer(&format!("hidden_{index}")), 0u32.into(), 1u32.into()),
                ));
                assert_eq!(resources.observable_facts_assuming_valid(&assumptions), expected);
            }
        });
        let (_, query_work) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(resources.observable_facts_assuming_valid(&assumptions), expected);
        });
        let (_, repeated_work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..16 {
                assert_eq!(resources.observable_facts_assuming_valid(&assumptions), expected);
            }
        });
        eprintln!("observable context investigation N={size}: one query={query_work}, 16 unchanged queries={repeated_work}, growing sequence={sequence_work}");
    }
}
```

An optimized userspace CPU profile of the frozen Adler2 checksum proof also
found 29.36% of samples inside this projection, predominantly called by
statement checking and fixed-state theorem application. These inclusive
samples are supporting evidence, not a portable performance criterion.

## Recommended repair and acceptance criteria

Retain a persistent observable composition and advance only affected resource
entries and support descendants. Private-local insertions and removals should
reuse its root when they do not change the observable view. A cache populated
independently for every source context is insufficient: it helps identical
queries but not the insert-and-project sequence above.

- Add a deterministic regression at four or more sizes that bounds unchanged
  queries independently of unrelated private locals, and bounds the growing
  sequence by approximately linear work up to indexing factors.
- Preserve the full source context's ownership, occurrence identities, support
  dependencies, and loan revocation. Filtering must retain the same semantics
  as the current support-descendant removal.
- Invalidate or update the derived view when addressability classification
  changes, including registry withdrawal, session reset, and registry restore.
- Cover addressed locals, composites, supported projections, and independent
  forks. Do not reuse proof decisions across different assumptions.
- Remove the redundant memory-fact enumeration while its algebra emits no
  observable facts.

Snapshot environment rebuilding is a separate hotspot. General fixed-state
proposition lowering still enumerates all locals, whereas Integer argument
lowering already selects referenced names. Extending that approach is a
promising subsequent investigation; this report concerns resource projection.
