# A fact set walks a shared snapshot's bound variables once per fact

Soundness: not soundness. The defect is extra work: building a fact set
does work quadratic in real time when its facts share one memory. Every
variable the set must reserve is still reserved, so freshness is unchanged.

Priority: P2.

`ProofFacts` reserves every variable its facts mention, free and bound.
Free variables come from `proposition_variables_reserving`, which skips a
snapshot the set already reserves and collects only the changed entries of
a snapshot derived from one. Bound variables come from
`collect_proposition_bound_variables`, whose memory case,
`collect_memory_bound_variables` (`src/kernel/reasoning/substitution.rs`),
walks every heap object, block and cell of the memory for every fact that
names it.

A function's entry states one loadability fact per object, each over the one
entry memory that holds every object. Master's regression
`facts_over_one_memory_reserve_its_variables_once`
(`src/scaling_tests/kernel/proof/facts/shared_memory_reservation_tests.rs`)
builds that shape at 16, 64 and 256 objects. It measures only persistent
work, which master keeps linear by collecting every fact's variables into
one plain set before the persistent inserts. The bound walk still visits
16 x 16, 64 x 64 and 256 x 256 cells (256, 4,096 and 65,536). A sequential
loop proof shows the same thing: each loop's new snapshot is walked whole,
including the block table, which gains one havoc marker per loop, so the
walk grows with the loops before it.

Reproduction: count the cells `collect_memory_bound_variables` visits while
`ProofFacts::from_ordered` builds the regression's facts at 16, 64 and 256
objects, and while `with_fact` adds one more fact over the same memory. The
count grows with the square of the objects, and the added fact walks the
whole memory again.

Invariant: the variables reserved for a fact set are exactly those of its
facts. Their collection is linear in the facts plus the entries in which
their distinct snapshots differ.

Acceptance: a fact set walks the bound variables of an interned snapshot at
most once. A snapshot derived from one already walked walks only the entries
it changed. A regression counts the visited cells at 16, 64 and 256 objects
and shows linear growth, plus no visits for a further fact over the same
memory. The lazy-reservation debug cross-check
(`CLICK_DEBUG_CHECK_LAZY_RESERVATIONS=1`) holds the reserved set equal to
the whole collection.
