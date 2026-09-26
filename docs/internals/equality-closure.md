# Equality closure (proposal)

Status: proposal, 2026-09-26. Nothing here is implemented. It inventories how
the kernel and the tactics handle equality today, names the defect class the
rbtree insert proof keeps hitting, and proposes replacing the per-site alias
handling with one congruence-closure structure in the kernel.

## The defect class

A proof establishes that two terms are equal, most often two spellings of one
pointer: a proof-arm binding `cid` and the C local `parent`, or `id` and the
parameter `p`. The kernel then files facts, owned cells, and load names under
whichever spelling produced them, and each lookup site decides for itself how
much of the equality to consult. Four gaps in the rbtree campaign are this one
class at four sites:

| Gap | Site | Local repair |
|---|---|---|
| 72 | read permission through an alias | `pointer_spellings` tries up to three spellings |
| 74 | a fold's body fact lowered under the other spelling | substitute one pointer variable by one exact alias and retry |
| open | fold consumption of cells owned under the other spelling | none; `without_fact_incrementally` never consults aliases |
| open | `have id->word == 5` after `p->word = 5` with `p == id` | none; load variables are keyed by exact pointer spelling |

Each repair is local, one hop, and different. The next proof that reaches a
new site, or a two-hop or displaced alias (`id + 8` against `p + 8`), finds
the gap again.

## Inventory

### Where equalities are stored

Everything lives in `PureFactContext` (`src/kernel/primitives.rs`, methods in
`src/kernel/assumptions.rs` and `src/kernel/assumptions/`). Contexts are
persistent (path-copying AVL maps in `src/persistent.rs`) and cloned at every
branch. One entry point, `assume_condition`, files a condition fact into every
index. There are about eight separate equality structures, split by sort:

- **Pointer blocks.** `pointer_block_aliases` (and a by-offset copy) record
  true cross-block `PointerEqual` facts, keyed by the exact full pointer,
  offset included. `exact_pointer_aliases` is deliberately one hop.
- **Pointer offsets.** `pointer_offset_aliases` (and a by-root copy) record
  same-block `PointerOffsetEqual` facts, one hop.
- **Pointer equality walks.** `has_indexed_pointer_equality_path` and
  `pointer_equality_component` search both alias indexes breadth-first. A
  third walk, `has_pointer_equality_path` (`condition_reasoning/order_paths.rs`),
  is not indexed. It rescans every condition fact at each frontier node, and
  it is the only place with a displacement rule (`a + d == b + d` from
  `a == b`). `simp`'s pointer decider and memory resolution use it.
- **32-bit equalities.** Three structures:
  - a lazy adjacency graph, `bitvector_equality_facts`, searched depth-first.
    It is discarded on every `assume_condition`, so the first query after an
    insertion rebuilds it from every condition fact.
  - `ConstantClasses`, the one union-find-like structure: union by size, with
    constants propagated to compound users. It grows only, and a withdrawn
    fact triggers a rebuild.
  - `exact_constant_equalities`, one hop.
- **64-bit equalities.** A separate persistent adjacency map,
  `bitvector64_equality_facts`, with a recursive walk capped at depth 128.
- **Algebraic equalities.** Constructor injectivity and no-confusion indexes,
  one hop. `AlgebraicEqual` is decided by exact lookup only, with no
  transitivity.
- **Ad-hoc congruence.** `bitvector_terms_equal_for_transport` and
  `pointer_offset_terms_equal_for_transport` recurse operand-wise over
  matching operators.

### Where terms are named

- **Load variables.** `mint_load_variable_identity` and the load-variable
  registry key a load by `(memory, pointer)` with the exact pointer spelling.
  `load(M, id + 8)` and `load(M, p + 8)` get two variables, with no equality
  stated between them. That is the `have id->word` gap.
- **Canonical forms.** `canonical_term` / `canonical_condition` are
  assumption-free and structural, so "equal canonical forms" means "same
  spelling".
- **Naming epochs.** `last_same_point` in the resource tracker is also
  assumption-free, and keyed by the exact pointer.
- **Minted pointers.** `resolve_minted_load_pointer` rewrites load variables in
  a pointer's offset back to loads by scanning every proposition fact on every
  call. It runs inside `pointer_spellings`, so on every resource read and
  write lookup.

### Where lookups miss a proved-equal spelling

- **Resource consumption.** In `without_fact_incrementally`, candidates come
  from `concrete_memory_start_candidates`, `direct_match_candidate_positions`
  (memory keyed by `base.block`, instances by identity), and
  `consume_fact_without_normalizing`. No step consults an alias. A comment
  states the assumption: "Snapshot-insensitive matching cannot change a pointer
  block". Composite and token arguments are compared up to proof;
  instance identity and memory bases are not.
- **Read and write permission.** These use the three `pointer_spellings`,
  then a full scan per spelling.
- **One-hop alias users.** Every caller of `exact_pointer_aliases` on its own:
  loans, heap retirement, memory resolution, validity checks. All of them miss
  two-hop and displaced aliases.
- **Load naming.** The load-variable registry, `known_value`, and
  `materialized_pointer_cell_load_variable` all use exact spellings.

### How tactics consume equality

- **`rewrite`, `assumption`, `normalize() using`, `apply ... using`.** These
  match premises exactly, up to orientation, canonical load form, and
  snapshot-blind buckets. None of them is transitive.
- **Known limits.** `normalize() using { a == b; b == c; }` cannot close
  `a == c`. That limit is documented in `examples/rbtree-model/README.md` and
  in the rbtree issue's pure-proof limits.
- **`simp`.** Transitivity exists only in `simp` and its kernel deciders, and
  only per sort: the pointer walk, the bitvector graph, and `ConstantClasses`.
  Only the algebraic constructor rules do anything congruence-like.
- **Kernel rules.** `PropositionDerivationRule` has no equality-substitution
  or transitivity rule. `rewrite` builds its new goal in surface code
  (`src/surface/checking/simp.rs`) and installs it with `refined_proposition`;
  I found no kernel re-check of the substitution. Whether a later certificate
  check re-derives it is an open question below.

### Conflicts with the efficiency contract

`docs/internals/verification-efficiency.md` asks that a simple tactic not scan
unrelated proof state and that derived relations be maintained incrementally.
Four structures above do not meet that:
- `has_pointer_equality_path`, which is O(facts × component);
- the equality graph, rebuilt after every insertion once it is queried;
- `resolve_minted_load_pointer`, which scans every proposition fact on every
  resource lookup;
- memo keys that clone whole terms.

## Proposal: one congruence closure in the kernel

An e-graph without saturation:
- hash-consed terms with stable ids;
- a persistent union-find over those ids;
- congruence closure: when two classes merge, parent applications whose
  arguments are now pairwise equal merge too.

There are no rewrite rules and no saturation. Classes merge only on equalities
the proof has established (hypotheses, `have`, executed assignments). A user
who wants another equation states it with `have`. Standard congruence closure
is O(n log n) over the merges on a path, which fits the efficiency contract.
Each query is a `find`.

### What goes in the graph

- **Pointers as terms.** A pointer is `ptr(block, offset)`, and offsets are
  normalized affine terms. With congruence, `id == p` gives `id + 8 ≅ p + 8`
  and `load(M, id + 8) ≅ load(M, p + 8)` without any displacement rule.
- **Loads as applications.** A load is `load(M, ptr)` with the memory snapshot
  as an argument. Congruence holds only within one snapshot. Carrying a load
  across a write stays frame reasoning (`transport`, the memory derivation DAG), which is
  explicit and outside the graph.
- **Bitvector and integer terms.** Operators are applications, so congruence
  subsumes the operand-wise "equal for transport" recursion. Each class
  carries its known constant, which subsumes `ConstantClasses` and
  `exact_constant_equalities`.
- **Algebraic constructors.** Constructors are applications. Merging two
  applications of one constructor merges their fields (injectivity). Merging
  two different constructors is a contradiction (no-confusion). Algebraic
  transitivity then comes free.
- **Pure function applications.** Applications of pure Click functions are
  ordinary applications, so `rb_parent_is(t, cid) ≅ rb_parent_is(t, parent)`
  holds by congruence. Gap 74's repair then becomes unnecessary.

### What stays out

- **Ordering, arithmetic, and disequality.** Ordering facts and arithmetic
  identities stay out: `a + 1 == b + 1` does not give `a == b`, and
  `(x & 1) & 1 == x & 1` is a normalization, not an equality. Disequalities
  are kept as a set of distinct class pairs, checked on merge.
- **Cross-snapshot equality.** Frame reasoning stays explicit, as above.

### Persistence and removal

Contexts fork at every branch, so the union-find, the use lists, and the
application table must be persistent, using the same path-copying maps the
context already uses. The graph is append-only. The inventory found fact
removal rare:
- `without_exact_fact`;
- `restricted_to_facts`, which planner premise selection and loans call about
  ten times in total.

A restricted context rebuilds its graph from the selected facts, at a cost
proportional to the selection. Facts about loads name their snapshot and stay
true after writes, so execution never needs to un-merge.

### Canonical keys

Every index that is keyed by a term today moves to class ids:
- resource consumption by base class;
- read and write permission by base class;
- load-variable minting by `(snapshot, class)`;
- condition-fact indexes by the classes of their sides.

A class's representative changes when it merges, so the indexes are keyed by
term id and resolved with `find` at query time. Alternatively, merges could
re-file the smaller class, which is n log n in total.

### Trust

The closure becomes part of the trusted kernel, as a decision procedure. It
must stay small and obviously correct: a classic congruence closure is a few
hundred lines. Wherever a certificate must justify an equality, the closure can
produce explanations: proof-producing congruence closure yields the chain of
input equalities and congruence steps. Adding a kernel equality rule that
checks such a chain would also close the open question about how `rewrite` is
checked.

### What it replaces

These would be deleted, not kept alongside:
- the pointer alias indexes and their one-hop accessors;
- the three pointer-equality walks;
- `pointer_spellings`;
- `resolve_symbolic_pointer_alias`;
- the lazy bitvector equality graph and the 64-bit adjacency map;
- `ConstantClasses` and `exact_constant_equalities`;
- the load-variable bridge DFS;
- gap 74's alias retry;
- the "equal for transport" recursions.

`resolve_minted_load_pointer`'s scan also goes: a minted load variable is
simply a member of its load's class.

### How tactics change

- **Exact tactics.** `assumption`, `apply ... using`, `normalize() using`,
  folds, and `have` goals match premises modulo the closure. A premise matches
  when its atoms are in the right classes.
- **`rewrite`.** It remains useful for directing a normal form, but it is no
  longer needed just to make two spellings meet.
- **Proof scripts.** The rbtree proofs lose most of their bookkeeping of the
  form `have parent == cid`, and `rewrite(X == c.model)` chains.
- **Behaviour change.** Some goals that fail today will pass. Diagnostics that
  print "not an available fact" should then name the two classes that did not
  meet.

## Staging

Each stage lands green, with its regressions and scaling tests at several
input sizes, as the efficiency contract requires for representation changes.

1. **Pointer closure.** Hash-consed pointer and offset terms and the persistent
   union-find. Replace the pointer alias indexes, the three walks,
   `pointer_spellings`, and `resolve_symbolic_pointer_alias`. Key resource
   consumption and permission by class. Regressions: the fold-at-arm-binding
   case from the rbtree insert frontier's `Right`-frame leaf, a two-hop alias,
   and a displaced alias.
2. **Loads.** Loads become applications. Load variables are minted per
   `(snapshot, class)`. Regression: `have id->word == 5` after `p->word = 5`.
3. **Bitvector terms.** Subsume the equality graph, the 64-bit map, constant
   classes, and the transport recursions.
4. **Algebraic terms and pure function applications.** Injectivity,
   no-confusion, and congruence through Click function calls. Delete gap 74's
   retry.
5. **Tactics and certificates.** Premise matching modulo the closure, a kernel
   equality rule for `rewrite` if the open question below says one is missing,
   and removal of the surface-side bridges.

Stage 1 alone unblocks the rbtree insert frontier's last left-left leaves.

## Open questions

- **How `rewrite` is checked.** Is the rewritten goal re-checked by the kernel
  anywhere, for example when a certificate is checked? If not, that is a trust gap
  independent of this proposal.
- **Offset normal form.** Congruence closure knows no arithmetic. `p + 8` and
  `(p + 4) + 4`, or `4*i + 8` and `8 + 4*i`, are different nodes unless
  something merges them. Then `load(M, p + 8)` and `load(M, (p + 4) + 4)` would
  not meet. The intended answer is to normalize every offset to one affine
  form at insertion: constants folded, terms reassociated and sorted by atom.
  That is sound under wrapping pointer arithmetic, and it composes with
  congruence: once `i ≅ j`, `4*i + 8` and `4*j + 8` merge. The open part is
  only whether `canonical_offset_term`, which today canonicalizes the loads
  inside an offset, already reaches a full affine normal form or needs
  extending.
- **Scaling.** How large do graphs get on the rbtree fixtures and the corpus,
  and does per-branch persistence cost stay within the contract? Stage 1 should
  measure this before the representation change spreads.
- **Diagnostics.** When a goal fails modulo the closure, what should the
  message show? Probably the two classes, with a representative member of
  each.
