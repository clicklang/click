# Decide equality with one e-graph in the kernel

P1. The kernel records facts, owned cells, and load names under whichever
spelling of a term produced them. Each lookup site then decides for itself how
much of a proved equality to consult. This keeps reappearing as proof failures
on true claims, and each local repair covers only one hop at one site. It also
blocks the Linux rbtree insert proof: see
[rbtree-example.md](rbtree-example.md), state of 2026-09-26.

The inventory and the design are in
[Equality closure (proposal)](../docs/internals/equality-closure.md). This
issue tracks building it.

## Violated invariant

Once a proof has established `a == b`, every kernel judgment about a term that
contains `a` must give the same answer for the same term with `b` in its place:
- fact availability;
- read and write permission;
- consuming owned cells or instances on a fold;
- the value of a load;
- decisions on C conditions.

The kernel must do this without the author restating the fact under the other
spelling, and at a cost that respects the complexity contract in
[Verification efficiency](../docs/internals/verification-efficiency.md).

Today it holds only in pieces, spread across about eight structures:
- one-hop pointer alias indexes;
- three different pointer-equality walks, one of which rescans every
  condition fact at each step;
- a 32-bit equality graph, rebuilt after every insertion once queried;
- `ConstantClasses`;
- a separate 64-bit adjacency map;
- exact-only algebraic equality.

Load variables are keyed by exact pointer spelling. The explicit tactics
(`assumption`, `apply ... using`, `normalize() using`, `rewrite`) match
premises exactly, up to orientation.

## Evidence

Four failures of this one class in the rbtree campaign:
- **Gap 72** (fixed locally in a3b96c12): read permission through an alias.
  `pointer_spellings` now tries up to three spellings.
- **Gap 74** (fixed locally in 4d5d6f6d): a fold's body fact lowered a frame
  identity through its proved-equal C local. Fixed by substituting one pointer
  variable with one exact alias and retrying.
- **Open, fold consumption.** `fold(rb_at(yid), ...)` cannot consume cells an
  unfold published under the loaded pointer's spelling ("fold requires
  ownership of the complete instance body"). `without_fact_incrementally`
  never consults aliases. This stops the `Right` great-grandparent leaves of
  the insert fixup's case-3 rotation, and the frontier in
  `examples/rbtree-insert/rbtree_insert.frontier` stands there.
- **Open, load after a store.** After `p->word = 5` with `p == id` proved,
  `have p->word == 5` holds but `have id->word == 5` is refused.

## Intended regressions

1. **Load through an alias after a store.** An mdtest where a frame resource
   names its cell by a model payload `id`, the C code stores through a pointer
   `p` loaded from memory, and the proof has `p == id`. Both spellings must
   then read the stored value:

   ```c
   struct node { unsigned long word; struct node *up; };
   void set_up_word(struct node *c) { struct node *p; p = c->up; p->word = 5; }
   ```

   ```click
   spec enum Frame { Up(struct node*, int) }
   resource frame_at(c: struct node*) {
       field model: Frame;
       match model {
           Frame::Up(id, value) => {
               owns &c->up;
               owns id->word;
               fact id != 0;
               fact c->up == id;
               fact id->word == value;
           },
       }
   }
   // proof: match f.model; unfold(f); step(); step(); step();
   //   have p == id by { simp(); }         -- holds today
   //   have p->word == 5 by { simp(); }    -- holds today
   //   have id->word == 5 by { simp(); }   -- refused today; must hold
   ```

2. **Fold at an arm binding over cells published under another spelling.** The
   same shape as the rbtree leaf: unfold a child reached through a load, then
   `fold` it at the proof arm's binding for that pointer. It must consume the
   cells.
3. **Two-hop and displaced aliases.** Given `a == b` and `b == c`, facts, cells,
   and loads at `a + 8` must be found through `c + 8`. The same must hold
   through an offset spelled two ways (`p + 8` and `(p + 4) + 4`).
4. **Explicit tactics modulo the closure.** `normalize() using { a == b; b == c; }`
   closes `a == c`. Today it cannot; see
   `examples/rbtree-model/README.md`, parent consistency.
5. **Scaling.** Deterministic curves over several input sizes for:
   - a chain of `N` pointer equalities;
   - `N` loads through aliases;
   - a proof with many branches that each add equalities.

   Work must be near-linear in the facts and terms a path adds. It must stay
   flat in unrelated ambient facts. Per-branch persistence must not clone the
   graph.
6. **Soundness negatives.**
   - Two terms that were never proved equal do not meet.
   - A merge of two different constructors, or of two distinct constants, is
     a contradiction, and nothing else.
   - Loads at different memory snapshots do not meet by congruence.

## Design constraints

These are settled in the design note:
- **No saturation.** Congruence closure over hash-consed terms with a
  persistent union-find. Classes merge only on equalities the proof
  established. A user who wants another equation states it with `have`.
- **In scope:** pointers, affine offsets normalized at insertion, loads
  applied to their memory snapshot, bitvector and integer terms, algebraic
  constructors (injectivity and no-confusion), and applications of pure Click
  functions.
- **Out of scope:** ordering, arithmetic identities beyond the offset normal
  form, and cross-snapshot frame reasoning. Those stay explicit.
- **Persistent and append-only.** Restricting a context to a premise selection
  rebuilds its graph from that selection.
- **Replace, don't add.** The structures the design note lists under "What it
  replaces" are deleted as each stage lands, including the gap-72 and gap-74
  repairs and the one-hop `resolve_symbolic_pointer_alias`.

## Stages

Each stage lands green with its regressions and scaling curves:
1. Pointer closure. Partly landed: pointer classes as a persistent union-find
   with offsets (`src/kernel/assumptions/pointer_classes.rs`), filed from
   every true cross-block pointer equality. Fold consumption retries a missed
   memory fact at the other spellings of its base
   (`mdtests/fold_through_a_pointer_alias.md`), and the two pointer-equality
   walks answer cross-block questions from the classes first. Still to do:
   - Move the remaining one-hop alias users (`exact_pointer_aliases`,
     `pointer_spellings`, `resolve_symbolic_pointer_alias`) onto the classes
     and delete them.
   - Same-block offset equalities. The walks still hold these, and deciding a
     same-block question by the affine normal form alone would equate offsets
     whose loads are still named by exact spelling. It changed
     `struct_wide_array_proof_expands_and_reverifies` that way, where
     `p + 24` and `(p + 8) + 16` both occur. So this waits for stage 2.
   - Both walks still exist.
   - The rbtree leaf's refold now finds its cells, but still fails to relate
     the child's pointer argument, loaded through the unfold's spelling, to
     `yid->rb_left`. That is load congruence, so the leaf needs stage 2.
2. Loads. Started:
   - A specification read that misses its exact cell looks the cell up at the
     other spellings of the address that the pointer classes give. So
     `have id->word == 5` after `p->word = 5` holds
     (`mdtests/load_through_a_pointer_alias_after_a_store.md`, with the
     negative `load_through_an_unrelated_pointer_rejected.md`).
   - Load *names* stay keyed by exact spelling. The load-variable registry is
     global across paths, so a name cannot depend on one path's equalities.
     Load congruence belongs in each path's reasoning, not in naming.
   - Open design point. A pointer loaded from memory is encoded as
     `source.block + load(M, source) × width`, borrowing the block of the
     spelling it was read through (`symbolic_pointer_load`). The same loaded
     value read through two proved-equal spellings therefore gets two
     representations whose difference is the spellings' base offset. That is
     what still stops the rbtree leaf: the child argument `yid->rb_left`
     evaluates to `yid.block + 4u`, while the unfold's reads gave
     `ugp.block + 4u`. The classes correctly refuse to call these equal.
   - Load congruence is unsound under that encoding. If `b == c` were derived
     for two loads of one cell through spellings whose bases differ by `d`,
     the two representations of the one stored pointer would differ by `d`.
   - Chosen direction: give every loaded pointer an opaque identity, the
     symbolic pointer named by its load. Every construction now goes through
     `Pointer::loaded` (landed, no behaviour change).
   - The flip is being prepared consumer by consumer. Its current state,
     the trial branch, and what still breaks are under "Handoff
     (2026-09-27)" below.
3. Bitvector terms.
4. Algebraic terms and pure-function applications.
5. Tactics modulo the closure, plus a kernel-checked equality rule for
   `rewrite`.

## Migration discipline

Each kind of thing moves onto the e-graph on its own, and every step lands
green. A step replaces a private mechanism with an e-graph query and
deletes the old code. It does not leave the old code running beside the
new.

The loaded-pointer encoding is the one change that cannot be split by
kind, because the whole kernel shares it. It is made small by doing the
risky part first:

1. **All producers through one constructor.** Done: `Pointer::loaded`.
2. **All consumers through one decoder.** `Pointer::as_loaded` answers which
   load a pointer is the value of. Each consumer that pattern-matches the
   storage-relative form moves onto it, one subsystem per commit, while that
   form is still in place. Candidates:
   - the naming decoders in `eval/memory_loads.rs`;
   - `resolve_minted_load_pointer`;
   - `observe` projections;
   - frame transport;
   - `rewrite` through a loaded pointer;
   - diagnostics.

   Step 2 is done when a trial flip breaks nothing that the flip itself does
   not explain.
3. **Flip the encoding inside the constructor and decoder** to the opaque
   form, and add reuse at load time: a load whose cell the path proves
   unchanged since an earlier named load takes that name.

If this stalls, a different representation of loaded pointers is on the
table; the constructor and decoder are what make trying one cheap.

### Provenance is a class attribute, not a spelling

The storage-relative form did two jobs at once: it named a loaded pointer,
and through its block it asserted where the pointer could point. That second
job was manufactured from the spelling it was read through, which is also why
it was inconsistent across spellings. An opaque identity asserts nothing, so
the trial flip lost every separation that rested on that implicit claim.

Provenance belongs to the value, so equality transmits it, and it is derived
from facts rather than from spelling. The rule it rests on:

> A pointer value obtained at snapshot S cannot point into an object whose
> address first became reachable after S.

- **Birth snapshot.** Recorded when a load is named: the snapshot it was read
  at. The class of equal pointers takes the earliest birth snapshot of its
  members, the stronger true claim.
- **Distinctness consults it.** A heap allocation, temporary, or local that
  did not exist at S is distinct from a pointer born at S. A local whose
  address is never taken is distinct from every pointer (landed: the
  never-address-taken case of this rule).
- **What it does not cover.** Code that finds facts, effects, or resources by
  exact block (the loop effect summary that `transport` no longer finds, for
  instance) needs lookup by pointer class, not provenance. The trial
  checklist is sorted into those two kinds.

## Handoff (2026-09-27)

The loaded-pointer flip (stage 2, migration step 3) is where the work
stands. Everything below is on master, green, unless it says otherwise.

### Landed toward the flip

In order. Each commit has its own regressions.
- `7f8eac4f` pointer classes (`src/kernel/assumptions/pointer_classes.rs`):
  a persistent weighted union-find over pointer blocks with an exact affine
  offset normal form.
- `9884ce02` a specification read that misses its cell retries at the other
  spellings the classes give.
- `56ce7b7c` and `82349436`: every loaded pointer is built by
  `Pointer::loaded` and decoded by `Pointer::as_loaded`.
- `69fec2b3` provenance: a local whose address is never taken is distinct
  from every pointer value.
- `9f0efd19` provenance: a loaded pointer is distinct from a local declared
  after the read (`loaded_pointer_predates_block` in
  `src/kernel/eval/memory_loads.rs`, consulted by `proven_distinct`).
- `387d9120` `rewrite` reaches through a loaded pointer to the load it names
  (`rewrite_through_loaded_pointer_block` in `src/surface/checking/simp.rs`).
- `4ab772fa` load congruence inside one snapshot: `load(M, p)` and
  `load(M, q)` are one value when the classes prove `p == q`
  (`PointerClasses::normal`, bounded by `LOAD_CONGRUENCE_DEPTH`).
- `d80a0f32` cross-snapshot equality at comparison time:
  `PointerClasses::proves_equal_in` also accepts two loads of one cell at
  two snapshots when memory reasoning proves the cell unchanged between
  them. This is frame reasoning, so it takes the path's facts and runs only
  when a comparison asks; it is never recorded in the classes.
- `08eb341f` two checks that assumed an indexed address adds a base term to
  its block: the common-base separation ladder now compares bare offsets
  of one block (`p[i]` against `p[j]` for a pointer that is its own block),
  and the alpha identity key expands a load variable in pointer-block
  position into the snapshot and address it reads. The latter needed
  `#![recursion_limit = "256"]` in `src/lib.rs`.

### The trial branch

Branch `egraph-loaded-pointer-flip` is master at `08eb341f` plus one commit,
`ea9de0ff`, holding the flip. It is not green and must not be merged. It
changes `Pointer::loaded` to return `Pointer::symbolic(load variable)`. A
pointer loaded from a cell that the path proves equal to an earlier load
reuses that load's name (`earlier_equal_load_variable` in
`src/kernel/eval/memory_loads.rs`). `Pointer::as_loaded` is still the old
decoder, so consumers that call it simply see no loaded pointer.

The loop is: diagnose one failure on the branch, land the general fix on
master green without the flip, rebase the branch, and remeasure. To measure
from a worktree of master:

```sh
git diff 08eb341f ea9de0ff > /tmp/flip.patch   # once
git apply --3way /tmp/flip.patch
export RUST_MIN_STACK=8388608
cargo nextest run --lib --bins --test documentation --no-fail-fast > unit.log 2>&1
cargo nextest run --test mdtests --test examples --test-threads 1 --no-capture \
    --no-fail-fast > md.log 2>&1
grep -E "^\s+FAIL" unit.log | sort -u
grep -oE "mdtest \`[^\`]*\` failed" md.log
git checkout -- src/
```

Counts over time: 34 mdtests and 29 unit tests at the first trial, then
22/27, now 16/20.

### What still breaks under the flip, at `08eb341f`

mdtests, grouped by what is known:
- `loop_frame_field_cells_at_constant_indices.md`: the loop's closer leaves
  `load(S2, G+0) == load(S3, G+0)` open, where `G` is the loaded
  `arena->occupied`. That is `occupied[0]` across the store `occupied[i]`
  with `2 <= start <= i`. Not yet diagnosed. Start by checking whether
  `store_cell_effect` separates `G@Constant(0)` from `G@4*i` under those
  facts; the bare-offset ladder of `08eb341f` should cover it.
- `loop_frame_through_two_hop_field_of_folded_state.md`: `transport` finds
  no frame evidence for `region->arena->occupied[k]`. The pointer is a load
  whose own block is a load. Not yet diagnosed.
- `rewrite_through_a_loaded_pointer_field.md` and
  `rewrite_pointer_base_inside_field_load.md`: `o->in` gets different load
  names on the two sides of the rewrite.
- `augment_rotate_callback.md`, `augment_rotate_callback_child_read.md`,
  `augment_rotate_callback_rejects_extra_write.md`,
  `augment_rotate_callback_rejects_consumed_shape.md`: stable-view
  separation. Views were separated by the block their loaded pointer
  borrowed, which the opaque form no longer supplies.
- Region and descriptor group, not diagnosed:
  `call_keeps_region_beside_folded_arena_state.md`,
  `call_keeps_a_region_cell_read_through_its_descriptor.md`,
  `unfold_region_after_writing_through_another_descriptors_pool.md`,
  `call_refuses_a_kept_view_that_may_alias_the_allocation_it_frees.md`.
- `shared_heap_detach_leak_diagnostic.md`, `shared_heap_two_parent_caller.md`:
  not diagnosed.
- `field_derived_precise_effect_after_metadata_write.md`,
  `load_through_a_pointer_alias_after_a_store.md`: not diagnosed.

Unit tests (20), not yet diagnosed:
- `kernel::tests::canonicalization_tests::pointer_loaded_from_an_opaque_cell_takes_a_canonical_offset`
  asserts the old encoding itself and is expected to be rewritten at the
  flip, not fixed before it.
- `kernel::tests::resource_scaling_tests::unfold_beside_descriptors_of_its_type_ignores_unrelated_descriptors`
- `surface::verification::artifact_identity_tests::field_derived_view_does_not_retarget_after_a_pointer_write`
- `surface::tests::project_tests::`: `truncated_service_step_reports_the_budget_not_a_missing_fact`,
  `perpetual_service_example_verifies_stably_across_repeated_runs`,
  `verifications_on_one_thread_are_independent`,
  `borrowed_slice_creates_only_canonical_terms`,
  `owned_split_buffer_carried_load_facts_stay_on_direct_proof_path`,
  `input_cursor_creates_only_canonical_terms`,
  `input_cursor_call_step_with_trailing_have_stays_on_proof`
- `surface::tests::expansion_tests::`: `branch_interface_service_simp_expands_and_rechecks`,
  `smart_have_expansion_plans_against_the_ordinary_surface_goal`,
  `source_expander_derives_separation_from_call_postconditions`,
  `scope_equality_chain_and_loaded_pointer_rewrite_expand_and_reverify`,
  `input_cursor_pipeline_has_no_outcome_fallbacks`,
  `expanded_step_uses_the_whole_context_for_frame_evidence`
- `surface::tests::scaling_tests::`: `a_fixed_store_proof_costs_the_same_after_a_growing_unrelated_proof`,
  `bounded_statement_successor_exclusion_ignores_unrelated_ambient_facts`
- `surface::tests::contract_tests::`: `following_c_if_splits_one_symbolic_call_successor`,
  `explicit_proof_if_does_not_capture_shared_following_c_if`

### How the last group was diagnosed

The loop-frame failures looked like a naming problem and were not. What
found the real cause was temporary `eprintln!` probes, gated on an
environment variable, run against one fixture both with and without the
flip, and diffed:
- `store_cell_effect` in `src/kernel/resource_tracker/step_effect.rs`: which
  store/cell pairs are separated, and by which rule;
- `load_variable_for_cell_with_origin` in `src/kernel/eval/memory_loads.rs`:
  which cell and snapshot epoch each load name stands for;
- `check_fixed_state_fact_transport_using_facts` in
  `src/surface/proof/fixed_state_proofs/fact_transport.rs`: the lowered
  source and target and the number of effect facts;
- the body-fact check before `BodyFactNotEstablished` in
  `src/kernel/functions.rs`, with the context's quantified facts.

Run one fixture with `MDTEST_FILTER=<name>` on the release build
(`cargo nextest run --release --test mdtests --no-capture`); debug builds
are slow enough to trip budgets. Remove the probes before committing.

### Things to watch

- **Naming stays assumption-free.** The load-variable registry is global
  across paths, and a name comes from the fact-free epoch walk
  (`cell_last_same_point`). The trial's `earlier_equal_load_variable`
  chooses among already-registered names using the path's facts. It
  returns that name in the path's value and registers nothing, but review
  that argument before landing it.
- **Scaling.** `earlier_equal_load_variable` scans every earlier load of the
  same address, which is linear per load and quadratic over a loop. It
  needs a scaling regression, and probably an index by pointer class,
  before it lands. `relabel` and congruence already have scaling tests in
  `pointer_classes.rs`.
- **Provenance, not spelling.** When a separation disappears under the flip,
  ask whether it rested on the borrowed storage block. If so, the fix is a
  provenance rule derived from facts (see the section above), not a new
  spelling.
- **Expansion tests pin routes.** A general fix can change which premises a
  smart tactic cites. `08eb341f` did so for
  `entry_alignment_premise_expands.md`. Keep what such a test guards by
  testing it directly, rather than restoring the old route.
- Judge green only from an unpiped `scripts/check.sh`.

After the trial is clean, the flip lands as one commit: the constructor, the
decoder, reuse at load time, and the rewritten encoding tests. Then the old
cross-snapshot offset machinery the classes replace can be deleted.

## Open questions (from the design note)

- **How `rewrite` is checked.** Its substitution is built in surface code, and
  no kernel derivation rule re-derives it. Stage 5 should add a checked
  equality rule, or show where the check already happens.
- **Offset normal form.** Whether `canonical_offset_term` already reaches a
  full affine form (constants folded, terms sorted), or needs extending.
- **Congruence timing.** Eager congruence on each merge, versus a batched
  rebuild when a contract or unfold adds many facts at once. Measure this in
  stage 1.
- **Failure diagnostics.** When a goal fails modulo the closure, show the two
  classes that did not meet, each with a representative member.

## Handoff from the DFS session (2026-09-26)

Two consumers and one soundness question for this work, found while scaling
contract entry. Nothing here changes the design constraints above.

- **Contract-entry view binding is quadratic until the closure exists.**
  `ResourceContext::view_occurrences_for_fact` (`src/kernel/primitives/resource_algebra.rs`),
  called once per view from `install_borrowed_contract_inputs`
  (`src/kernel/api.rs`), scans every candidate in the block bucket and runs a
  full `memory_range_covers` per pair, because it must refuse ambiguous
  bindings. All pointer parameters share the `ExternalArgument` block, so the
  bucket is every range. No existing key is complete for the five positive
  routes of `memory_range_covers`: constant base delta,
  `pointers_proven_equal_for_memory_resolution` (offset-equal facts, pointer
  equality paths, constant pinning), load bridging, order-derived
  containment, and `range_covered_by_fact_range`. Once pointer classes are the
  one equality method, the candidates for a requirement can be restricted to
  its class, with the full scan kept wherever a route reads something the
  closure does not. The scaling test
  `contract_entry_with_many_views_beside_an_owner_is_not_cubic`
  (`src/surface/tests/scaling_tests.rs`) has a quadratic ceiling that should
  become near-linear then.
- **Order facts relate pointer bases inconsistently.** Under
  `requires p <= q; requires q <= p;`, the contract
  `owns p[0..1]; owns q[0..1];` is accepted at entry, while the same contract
  with `requires p == q` is refused as ambiguous. Some coverage routes read
  order facts and the partition check does not. Ordering is out of scope for
  the closure, so either antisymmetry must be excluded from equality routes
  consistently, or a proved `p <= q and q <= p` must merge `p` and `q` like any
  other proved equality. This yields no false theorem. Contract entry is
  fail-open by design: it assumes the caller, so it refuses only a proven
  overlap. Every consumer (calls, returns, folds, and refinement through
  `loans::plan_stable_view_transfer_with_bindings_and_composites`) reserves
  each owned requirement from what is actually held, and neither overlap
  detection nor coverage uses order antisymmetry, so an order-equal
  precondition is unsatisfiable. Regressions:
  `mdtests/order_equal_pointers_do_not_supply_two_owners.md`,
  `mdtests/order_equal_indices_do_not_carve_two_owners_from_one_array.md`, and
  `mdtests/a_return_cannot_produce_two_owners_of_order_equal_pointers.md`.
  The closure still has to choose between merging on proven antisymmetry and
  excluding it consistently.

## Acceptance criteria

- Regressions 1 through 6 pass under `scripts/check.sh`, and `click audit`
  agrees with `click verify` on them.
- The insert frontier's two case-3 leaves under a `Right` great-grandparent
  frame complete. `tests/examples.rs` moves its pinned frontier accordingly.
- The replaced structures are deleted, not bypassed. Proofs that restated a
  fact under a second spelling only to reach a lookup site, such as the
  frontier's `have ... parent) == 1` and `rewrite(cid == parent)` bridging,
  can drop that bookkeeping.
- `docs/internals/equality-closure.md` becomes the description of the built
  design rather than a proposal. The concept docs describe premise matching
  modulo proved equalities.
