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

## Why it was not fixed with the proved case

A proved query can stop at the members its sides' roots nominate, because
any pair those members hold is a pair the full scan admits. A refusal needs
every member that could hold a side to answer no, and the containment
question is answered by the general decision procedure
(`pointer_element_index_from_base_with_width` asks `decide` whether two
offsets are equal), which can relate offsets with different roots through
facts. Skipping members at unrelated roots would therefore change the
verdict only where such facts exist, but nothing yet shows the routes'
candidate sets are complete, so the scan stays.

## Acceptance criteria

- A candidate index for the three routes whose completeness is argued from
  the containment rules (which bases a member's containment proof can
  relate), or a containment relation restricted to what such an index
  serves, with the verdict argument written beside it.
- The reproduction above refuses the requirement with requirement-checking
  work independent of `N` up to indexing factors, pinned by a deterministic
  regression at four sizes.
- No example or mdtest changes its verdict.
