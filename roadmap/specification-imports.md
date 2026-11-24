# Precise import-aware `--changed-since`

Priority: P2.

Soundness: not soundness. This is tooling efficiency. `click verify
--changed-since` already rebuilds the whole selected entry scope of any sidecar
with Click imports, so a changed import cannot leave a stale verdict marked
current; the remaining work only avoids rebuilds.

Modules and imports are delivered: transitive local imports, project roots,
module-owned names and spans, file/location/project selection that assumes
imported theorem statements and contracts without running their proofs, and
imported named contracts, C function specifications and tactics
([sidecars](../docs/concepts/sidecars.md#local-specification-imports),
[verify](../docs/reference/cli/verify.md)). An imported file's `verifying`
declarations apply only when that file is verified itself.

## Current behavior and violated invariant

`imported_project_rebuild_reason` in `src/bin/click-verify.rs` returns a
rebuild reason for every project with more than one module (and for any
project with a C profile). `--changed-since` then selects every proof the
entry owns, reuses none, and records no reusable incremental marker
(`imported_projects_force_the_documented_selected_scope_rebuild`;
"For a sidecar with Click imports" in
[verify.md](../docs/reference/cli/verify.md)).

Change selection should scale with what changed: an edit to an imported
declaration should reselect only the entry's proofs that depend on it, and an
unrelated change to an imported file should reselect nothing.

## Intended regression

An entry importing a library, with several entry proofs of which only some use
a given imported theorem, predicate or contract. After an attested baseline:

- changing that imported declaration's statement selects exactly the proofs
  that use it;
- changing an unrelated imported declaration, or only an imported proof body,
  selects no entry proof;
- changing an import edge (adding, removing or retargeting an `import`)
  conservatively reselects the entry scope.

## Acceptance criteria

- `--changed-since` on a sidecar with imports records and reuses an
  incremental marker covering every reachable module and import edge, and
  selects proofs by dependency on changed imported declarations.
- It never executes an imported proof because its declaration changed, and
  never leaves a dependent result marked current after an imported change.
- Selection work is proportional to the changed declarations and their
  dependents, with a deterministic regression over several module and proof
  counts.
- `docs/reference/cli/verify.md` describes the precise behavior in place of
  the fallback.
