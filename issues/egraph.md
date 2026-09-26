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
3. Bitvector terms.
4. Algebraic terms and pure-function applications.
5. Tactics modulo the closure, plus a kernel-checked equality rule for
   `rewrite`.

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
