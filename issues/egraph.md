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
   - Measured, then reverted: flipping `Pointer::loaded` to the opaque form
     broke about 29 unit tests and 34 fixtures. The common cause is that the
     kernel relates a pointer loaded at one snapshot to the same pointer
     loaded at another through machinery that compares load terms inside
     offsets across snapshots (frame reasoning over an unchanged cell). With
     opaque identities those become two blocks compared exactly, and that
     machinery no longer applies.
   - So the opaque form needs a bridging rule first: two loaded pointers are
     equal when memory reasoning proves their loads equal. Resource lookup
     and pointer comparison must consult that rule, not only exact block
     identity. That design is the next open step of stage 2.
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
  other proved equality. A separate agent in the DFS session is checking
  whether this yields a false theorem and fixing the partition check; its
  result will be recorded here.

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
