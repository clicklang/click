# A refused call separation requirement scans the owned frame

Soundness: sound. The cost is in refusing: the check emits the requirement
as an obligation exactly when no route proves it, and no route proves more
than its own premises support. Only the work grows with unrelated state.

A verified call's separation requirement that the caller's context does not
establish is refused only after three resource-separation routes have asked
every owned member of the requirement's block whether it holds each side:
the composition law (`ResourceContext::separated_owned_members_in_block`,
whose nominated-first selection answers a proved query from the members at
the sides' roots and falls back to the whole block to refuse),
`ResourceContext::proves_owned_resources_separate` (the block bucket of
`direct_match_candidate_positions`), and the interval cover of
`ResourceContext::owned_memory_ranges_separate_from` (every fact of the
composition). Each answer is a proof-aware containment question
(`range_covered_by_fact_range`). Every object a pointer parameter reaches
shares the `ExternalArgument` block, so a refusal costs the caller's whole
owned frame. The complexity contract
(`docs/internals/verification-efficiency.md`) requires a simple tactic not to
scan proof state unrelated to its operands.

## Reproduction

Shape of `call_separation_requirements_ignore_unrelated_owned_objects`
(`src/scaling_tests/surface/tests/scaling_tests.rs`), with `N` unrelated owned
objects:

```c
struct node { struct node* left; struct node* right; int32 size; };
void callee(struct node* a, struct node* b);
void caller(struct node* a, struct node* b, struct node* q0, ...) { callee(a, b); }
```

```click
verifying "owners.c";
extern void callee(struct node* a, struct node* b) {
    views a->left;
    owns b->size;
    requires separate(memory(a->left), memory(b->left));
}
void caller(struct node* a, struct node* b, struct node* q0, ...) {
    owns a->left;
    owns b->size;
    owns q0->left;
    owns q0->size;
    ...
} by {
    step();
    step();
}
```

`CLICK_TIMINGS=1 click verify` charges the first `verified call requirement
checking callee` 2,681, 4,765, 8,933 and 17,269 units at `N` = 2, 4, 8 and 16
(release build, 2026-10-15, after the fix for the proved and null-guarded
shapes), about 1,000 units per unrelated object, nearly all in
`resource separation: owned resources`, `composition covers` and
`composition members`.

## Why no candidate index is complete today

A proved query can stop at the members its sides' roots nominate, because
any pair those members hold is a pair the full scan admits. A refusal needs
every member that could hold a side to answer no. A member holds a side when
`pointer_element_index_from_base_with_width` relates the side's address to
the member's base, and three of its routes relate offsets whose roots
(`memory_base_root`) differ and are tied by no exact alias:

- `decide(PointerOffsetEqual(4*i, 4*j))` reaches the difference graph, whose
  `offset_equality` asks `Bitvector32Equal(i, j)`; order facts `i <= j` and
  `j <= i`, or both values pinned to one constant, decide it. Pointer
  parameters are `Int32Scaled { Variable, 4 }`, so this is their shape. A
  kernel probe over a composition owning `4*i[0..3]` and `4*k[0..3]` proved
  `4*i[0..3]` contains `4*j[1..2]` and `separate(4*j[1..2], 4*k[1..2])` with
  both orders stated, and refused both with only `i <= j` (2026-10-15).
- The difference graph's pointer union-find closes equalities transitively:
  with `requires a == r; requires r == q;`, a member `q[0..1]` holds
  `memory(a[0..1])`, which one-hop exact aliases do not nominate (seen at
  source level with a tracing build).
- Memory resolution (`pointer_offsets_proven_equal_for_memory_resolution`
  through `stored_value_at_equal_pointer`) equates a loaded pointer with the
  pointer stored in its cell, so a side spelled through a load is held by a
  member at a parameter's base. In the mdtest corpus a tracing build saw 22
  acceptances by members outside the nominated roots (8 deciding the pair),
  all of this or the scaled-equality shape; the rbtree, arena and
  linked-list examples saw none outside, and their verdicts were unchanged.

A key complete for these routes would have to follow difference-graph
equalities (including two values pinned to one constant), the pointer
union-find's transitive classes, and memory resolution's load-to-stored
value equalities, none of which is indexed by root today.

## Smallest kernel changes that would allow it

Either keeps `decide` unchanged in what it proves:

1. Maintain, beside the difference graph and pointer union-find, a
   persistent relatedness index over offset root atoms: union the atoms of
   both sides of every int32 or pointer-offset fact that relates two
   non-constant atoms, file atoms with a pinning constant bound under that
   constant, and mark load-rooted atoms (registered loads) as related to
   every stored pointer. A refusal then asks the members filed under the
   side's related atoms, the constant-root bucket, and the load-related
   members. Load-rooted frames such as the rbtree examples would still read
   most of their members.
2. Or make the composition routes' cross-root containment read only the
   resource context's canonical address index (`memory_addresses`, kept in
   the equality graph's canonical classes), so that index is complete by
   construction. This changes what those routes prove and needs the corpus
   and an approval before it lands.

## Acceptance criteria

- One of the changes above, with its completeness argument written beside
  the index and a test-only cross-check comparing the indexed refusal with
  the full scan over the separation tests and the corpus.
- The reproduction above refuses the requirement with requirement-checking
  work independent of `N` up to indexing factors, pinned by a deterministic
  regression at four sizes.
- No example or mdtest changes its verdict.
