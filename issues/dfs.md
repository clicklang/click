# Verify a pointer-chasing search over an index array (the "DFS" example)

P1. This issue tracks the DFS forcing-function example. Its acceptance
criteria are met; what remains is proof cost, measured below as the basis for
deciding whether to close it. `design/dfs-gaps/` holds the saved reductions
and design notes and is deleted with this issue. Keep the user's constraints:
the C is fixed, no proof hacks, and a true claim Click cannot prove is a
Click gap.

## Acceptance (met)

- `mdtests/search_terminates_by_unmarked_count.md`: the unchanged
  `next`-chasing loop terminates on `decreases unmarked(visited, 0, n)`, is
  memory safe, and `result == 1` implies an in-bounds, unmarked target reached
  by a finite `walk`.
- `mdtests/branching_graph_dfs.md`: the unchanged cyclic two-successor
  recursive search terminates, is memory safe, a nonzero result gives a finite
  `Path` in the entry graph to an in-bounds target unmarked at entry, and from
  an all-unmarked entry state zero means no finite path reaches the target.
- `mdtests/sweep_maintains_a_zero_unmarked_count.md`: a marking loop keeps
  `unmarked(visited, 0, i) == 0`.
- Shared checked modules: `mdtests/unmarked_count_lemmas.click`
  (`unmarked_nonnegative`, `unmarked_frame`, `unmarked_point_update`) and
  `mdtests/branching_graph_paths.click` (`Path`, `walk`, `walk_frame`,
  `closed_marks_exclude_target`, `exhausted_zero_entry`). The mdtest gate
  verifies each `.click` file as an entry.

## Step 4 of the fold read-range design (landed)

`design/dfs-gaps/fold-read-range-inference.md` step 4 removed the sweep's
prefix-frame scaffolding: one explicit `transport` carries
`unmarked(visited, 0, i) == 0` across `visited[i] = 1` through the kernel's
fold read frame. The same pass removed bookkeeping the other recent
capabilities make obsolete: C-proof `apply` now selects premises (including a
stated range's extent halves) instead of restating them, reflexive transport
sources and constant-true premises need no `have`, loop-head extents need no
`have`, and restatements of call guarantees are gone. The DFS point-update
lemma stays: its store is inside the counted range.

| File | Lines before | Lines after | C-proof work before | after |
| --- | ---: | ---: | ---: | ---: |
| `sweep_maintains_a_zero_unmarked_count.md` | 113 | 88 | 80,122 | 68,499 |
| `sweep_prefix_survives_its_endpoint_store_by_transport.md` | 82 | deleted (now identical to the sweep) | | |
| `search_terminates_by_unmarked_count.md` | 369 | 309 | 69,611 | 53,172 |
| `branching_graph_dfs.md` | 1,147 | 587 | 424,502 | 411,941 |
| `branching_graph_path_witness.md` | 202 | 21, plus 185 in `branching_graph_paths.click` | | |
| `unmarked_count_lemmas.click` | 440 | 273 | 71 ms | 41 ms |

Work is deterministic units summed over the C proof's tactics
(`CLICK_TACTIC_WORK_REPORT`); pure-theorem tactics are not instrumented, so
the lemma library shows wall time. The DFS lost 560 lines mostly by importing
the two modules instead of copying their lemmas. `unmarked_monotone` and
`unmarked_after_first_call_decreases` had no user and were deleted.

## Quantified frames (landed)

`src/kernel/quantified_frame.rs` carries a quantified fact across stores and
checked call write sets as one checked `transport`, reading the context's own
facts under a fresh binder and the fact's guard; `simp` reaches it for
`at(label, x) == x` as it did for `old(x) == x`
(`docs/internals/resource-tracker.md`, "Quantified frames are checked facts,
not names"). The DFS framing of `left`/`right`, the `visited` frame for
`k != cur` and the point-update halves, and the completeness proof's six
snapshot instantiations and their rewrites are gone; so are the search's
reflexive `have`s and repeated frame premises.

| File | Lines before | after | C-proof work before | after |
| --- | ---: | ---: | ---: | ---: |
| `branching_graph_dfs.md` | 587 | 487 | 411,737 | 472,749 |
| `search_terminates_by_unmarked_count.md` | 294 | 238 | 35,062 | 46,079 |

"Before" is the previous proof on the previous kernel; on the new kernel the
previous proofs cost 423,359 and 37,827. The explicit quantified transports
cost more than the per-index ones they replace (about 10k units each where a
read's history is not recorded, so the leaf falls back to the single-fact
transport).

## Where the remaining proof text goes

Measured before the quantified frame; its framing rows are what it removed.

`branching_graph_dfs.md`, 587 lines (about 555 of Click):

| Category | Lines | Kind |
| --- | ---: | --- |
| Failure completeness: compose the two calls' closure summaries, then `exhausted_zero_entry` | ~128 | half inherent; ~70 are instantiations of snapshot equalities for `left`/`right` |
| Framing `visited` across the marking store (target cell, prior marks, prefix/suffix for the point update, `k != cur`) | ~80 | bookkeeping |
| Success paths: open the callee's witness, prepend the edge, frame the path to the entry graph | ~63 | ~40 inherent, rest framing |
| Framing read-only `left`/`right` across the store and the left call | ~60 | bookkeeping |
| Composing call guarantees (target cell unchanged, `cur` still marked, `marked_transitive`, opening `left_result == 0 implies ...`) | ~56 | mixed |
| Ranking arithmetic (point update, nonnegativity, strict decrease, chains through `old`) | ~43 | mostly inherent |
| Early returns (vacuous failure summaries, `Path::Here`) | ~35 | inherent but trivial |
| Resource declaration and `marked_transitive` | ~28 | inherent |
| Contract statement (8 `ensures`) | ~26 | inherent |
| Resource re-observation and successor-bound instantiation for call arguments | ~22 | bookkeeping |

Representative framing text (repeated for `right` and again across the call):

```click
have forall (k: int32) {
    0 <= k and k < n implies old(left[k]) == at(after_mark, left[k])
} by {
    intro(); intro();
    extract(0 <= k); extract(k < n);
    transport(old(left[k]) == old(left[k]), old(left[k]) == at(after_mark, left[k])) using {
        old(left[k]) == old(left[k]);
        0 <= k; k < n;
        separate(memory(left[0..n]), memory(visited[0..n]));
    };
    assumption();
}
```

and, in the completeness proof, six instantiations of the form
`instantiate(forall (k) { ... old(left[k]) == at(before_right, left[k]) }, k)`
followed by `rewrite`s from `old(left[k])` to the snapshot the callee spoke
about.

`search_terminates_by_unmarked_count.md`, 309 lines: `walk` and its two
theorems 96 (`walk_frame` alone 56, used only to frame `next` across the
`visited` store), framing `next` across the store 40, framing `visited` for
the point update 44, witness extension 16 (half framing), contract, loop
header, and ranking 42, setup and statement steps 25.

What a language or tooling change could remove, largest first:

1. **Array arguments that agree on `0..n`** (both `walk_frame`
   applications in the DFS, `walk_frame` in the search). `left` and
   `at(after_mark, left)` are different arrays: parameters share one block,
   and a caller may pass `visited == left + n`, so the store changes `left[n]`.
   They agree on `0..n`, and `walk_frame` is the real theorem that `walk`
   reads nothing else. Removing it needs a checked "agree on `[lo, hi)`"
   relation that pure functions can consume, not a name.
2. **A store's frame as one checked fact** — landed as the quantified frame
   above.
3. **Path-condition use of call guarantees** (about 25 DFS lines). Inside the
   branch where `left_result == 0`, opening `left_result == 0 implies X`
   takes an `extract`/`assumption` block each time.
4. **Pure-theorem extent halves** (resolved). A listed `views`/`viewable`
   range premise in a pure `apply … using`, including an induction
   hypothesis's, cites its extent halves wherever they are available, by the
   shared `cite_range_extent_guards` rule, so the lemma library no longer
   restates `0 <= n - lo; n - lo <= 1073741823`
   (`mdtests/induction_hypothesis_cites_a_listed_range_with_its_extent.md`;
   a moved range whose halves nobody established is still refused,
   `mdtests/induction_hypothesis_owes_the_range_extent.md`).

The remaining ~250 DFS lines (contract, ranking, witness construction, the
closure-summary case analysis) are the claim's own content. Item 2 has
landed and the DFS is 487 lines; item 1 is a language question, and without
it the remaining text is dominated by inherent content, which is a reasonable
point to close this issue.

## Findings from the step 4 pass (reported, not filed)

- `click expand` on a C mdtest that imports a local `.click` module failed
  with the imported declarations unknown; fixed on this branch (commit
  "Load an importing C mdtest as a project in click expand") with a
  regression in `src/bin/click-expand.rs`.
- In a pure theorem, smart `apply(walk_in_range(a, n, from, previous));`
  refuses a `views` requirement with "`0 <= n is true` is not an available
  fact" after `have 0 <= n`, `have 0 <= n - 0`, and
  `have n - 0 <= 1073741823` all succeed; the explicit `using` form passes.
  The search selected a candidate its checker rejected.
- The loop's `close_invariants()` closes the quantified `next` bound itself
  when its explicit transport is omitted, but its work rises from about 13k
  to about 250k units; the search keeps the explicit transport.
- Diagnostics: a smart C-proof `apply` missing a `viewable` premise says only
  that the preservation driver declined it; a missing
  `at(iter, viewable(...))` is rendered identically to the available current
  `viewable(...)`; a `simp` refusal about `visited[k]` after a store to
  `visited[cur]` says the store to `next[…]` may have written it.
- `unfold(...) using` still refuses a constant-true premise such as `0 <= 0`
  that `apply using` now accepts; `n <= n` is not constant-folded and still
  needs a `have`.
