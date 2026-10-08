# `click audit` does not see smart tactics inside most `have` bodies

## Violated invariant

`click expand` must not disagree with `click profile` or `click audit`
(`AGENTS.md`, "Tooling stability comes first"). Every smart tactic `click
expand` can select must be in the inventory the other two walk.

`click expand FILE:LINE` selects a smart tactic at any depth, through a table
of every written tactic (`f0c7bebe9`, "Select smart tactics for expansion by
source span at any depth"). `click audit` still builds its inventory from the
flat per-claim index, which does not descend into a `have` body, and
`click profile` counts smart source sites with the same inventory. A `have` counts as one smart site only when its whole body is
`simp`, optionally after predicate `unfold`s; any other `have` is a container
and its body is not searched.

## Reproduction

```click
theorem helper(x: int32) {
    requires 0 <= x;
    ensures 0 <= x by { assumption(); }
}

theorem two_sites(x: int32) {
    requires 0 <= x;
    ensures 0 <= x by { apply(helper(x)); }
    ensures 0 <= x by {
        have 0 <= x by { apply(helper(x)); }
        assumption();
    }
}
```

`click expand` rewrites the bare `apply` on each of the two lines that hold
one, and both results verify. `click audit` on the file reports
"1 sites discovered". A file whose only smart tactic is
`have P by { arithmetic() using { ... } }` audits as "0 sites discovered".

A text scan of mdtests, examples, stdlib and integrations on 2026-10-07 found
about 2,000 `have` bodies that hold a smart tactic and are not in the
inventory, against about 1,000 that are. That is a regular-expression
estimate, not the tool's count.

## Effect

`click audit` expands a wholly selected claim once, with all its sites, and
that expansion does rewrite the tactics inside `have` bodies, so for most
claims they are checked. They are not checked for a claim audited a site at a
time: one whose whole-claim expansion fails, or one selected in part by
`--start-at`, `--max-sites` or `--changed-since`. The smart-site count
`click profile` derives from the inventory leaves them out.

## Intended change

Build the inventory in `collect_smart_script_sites`
(`src/surface/expansion.rs`) from the same any-depth table that selection by
location uses (`have_body_tactic_entries` and `block_tactic_entries` in that
file), so the three tools list the same sites.

## Acceptance

- The file above audits as 2 sites, and each passes.
- `smart_site_inventory_is_the_same_for_a_one_tactic_proof_and_its_block` in
  `src/surface/tests/expansion_tests.rs`, or a test beside it, checks that a
  smart tactic inside a `have` body with other steps is in the inventory.
- The smart-site count `click profile` derives from the inventory includes it.
