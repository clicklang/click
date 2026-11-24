# `click audit` command

`click audit` checks three promises Click makes about every proof in the
selected proof containers. Each audit ends with one headline: how many of the
items it checked fail.

| Audit | Checks | Items |
|---|---|---|
| `expansion` | every smart tactic expands to a simple proof that verifies | smart-tactic sites |
| `raise-lower` | every fact and goal a step holds raises to Surface syntax that lowers back to the same term ([raise-lower principle](../../internals/raise-lower-principle.md)) | distinct facts and goals |
| `fact-stability` | lowering never depends on the facts available ([fact-stable lowering](../../internals/raise-lower-principle.md#lowering-is-fact-stable)) | lowerings |
| `legacy-walk` | no read is named by the legacy version walk over memory snapshots ([legacy-walk audit](#legacy-walk-audit)) | walk queries |

With no audit named, the first three run on the same target and the run ends with
an `AUDITS:` block of their headlines. Only the expansion audit's failures
fail the command; the lowering audits are tracked.

## Synopsis

```text
usage: click audit [expansion|raise-lower|fact-stability|legacy-walk] [OPTIONS] <sidecar.click|example-project|examples-directory|mdtest.md|mdtests-directory|repository-root>
```

## Lowering audits

`raise-lower` and `fact-stability` verify each selected proof container once,
on its own verifier thread, with their records on. They write
`raise-lower.tsv` and `fact-stability.tsv` under `--records DIR` (default
`target/click-audit`); each record's last field names its container.

The raise-lower headline counts a fact once per container, claim and
rendering, however many steps restate it. A fact fails when it has no raised
form (`unraised`), its raised form does not lower (`unlowered`), or it lowers
to another term (`differs`) or the other polarity of the same comparison
(`polarity`). A pure proof (a theorem, a lemma, a termination check) raises
and lowers in its own context; a program proof's fact at no fixed program
state cannot be raised there and is reported as not checkable. The fact-stability headline counts lowerings
whose term facts changed (`differs`) or among whose paths facts chose
(`paths`); `refused` lowerings are tracked.

### Reading and reproducing failures

After its headline, a lowering audit prints its first ten failures in full:
the outcome, the claim (raise-lower) or lowering site (fact stability), the
container, the fact as rendered, its raised form or fact-free lowering, what
that lowered to for `differs`, and a command that reproduces just that
failure:

```text
raise-lower audit: 4 failing of 22 facts checked (18.2%); 6 not checkable (no fixed state); ...
  4. unraised in `arena_release.contract` (mdtests/arena_prefix_free_reads_region_arena.md)
       fact: viewable((byte_offset(old(region->arena), s * 4) as (uint8 *))[0..(e - s) * 4])
       reproduce: click audit raise-lower --claim arena_release.contract mdtests/arena_prefix_free_reads_region_arena.md
```

Every failure, with its reproduce command, is in `raise-lower.failures.tsv` or
`fact-stability.failures.tsv` beside the records: outcome, container, claim or
site, fact, raised form or fact-free lowering, lowered form, command. A
reproduce command audits only that container, and `--claim CLAIM` (repeatable)
counts and lists only that claim's raise-lower facts. The expansion audit
prints a reproduce command for each failing site, and writes every failing
site or container to `expansion.failures.tsv` in the same columns.

Each `raise-lower.tsv` record ends with the reasons the raiser noted for
reads it could not spell while raising that fact, separated by `; ` (the
eleventh field, empty when it noted none):

| Reason | Meaning |
|---|---|
| `point read: its version point has no name` | the read's version point is no recorded point, so no selector names it |
| `point read: the recorded state at its point selects another version` | the point is named, but a read there names the cell at another version |
| `point read: no place spells its cell at its point` | no declaration or address expression spells the cell |
| `snapshot read: its memory matches no recorded point (read site: yes\|no)` | a memory-named integer read whose memory no recorded point reads |
| `snapshot read: the recorded point with its memory names the cell differently` | the point is found, but its own read of the cell is another term |
| `snapshot pointer load: ...` | the same, for a memory-named pointer load in a pointer comparison |
| `pointer load at a point: ...`, `pointer load at a snapshot: ...` | a loaded pointer inside an address that no route spelled, with whether its point is named or its memory matches a recorded point |

Count them over a run with, for example,
`awk -F'\t' '$1 != "same" && $11 != "" { n[$11]++ } END { for (r in n) print n[r], r }' raise-lower.tsv`.

A container that does not verify as its expectation says is counted after
the headline and listed in `raise-lower.unexpected.tsv` or
`fact-stability.unexpected.tsv`. The audit does not judge it: the gate and the
nightly tests own verification verdicts.

## Legacy-walk audit

`legacy-walk` runs only when named. Like the lowering audits, it verifies each
container once on its own thread and writes `legacy-walk.tsv` under
`--records DIR`. It counts every query that names a read with the resource
tracker's assumption-free version walk over memory snapshots
(`resource_tracker::last_same_version_point` and the entries beside it). The
[program-point migration](../../internals/memory-dag.md) replaces that walk
with versions the program point carries, and the walk is deleted once this
count reaches zero. A query is counted once, at its outermost entry, against
the source line that called that entry.

Each record is `queries, work, site, resource, storage, extent, container`:
how many queries one container made from one call site for one kind of read
(`cell` or `block`, the storage class of its block, and the cell's width),
and the deterministic work they charged. Work is zero for queries made while
the caller runs uncharged. The headline sums the queries, their work, the
distinct call sites, and the containers with any query. After it, the audit
lists the call sites and read kinds with the most work first, then the most
queries, each with the container that made the most of them. On `examples/` at the change that
added it:

```text
legacy-walk audit: 83943 queries named a read with the legacy version walk, charging 488727 work units, from 8 call sites in 136 of 156 proof containers; records: target/click-audit/legacy-walk.tsv
  1. 641 queries in `src/kernel/memory_history.rs:5656` (examples/bounded-pool/bounded_pool.click)
       read: cell external 4
       cost: 106306 work units in 93 containers
       reproduce: click audit legacy-walk examples/bounded-pool/bounded_pool.click
```

`legacy-walk.failures.tsv` and `legacy-walk.counts.tsv` sit beside the
records in the lowering audits' columns; the counts file also has each read
kind's query total, `work` and `sites`. The audit never fails the command.

## Expansion audit

The expansion audit inventories source-addressable smart tactics, expands
selected sites, verifies each rewritten proof unit, and checks that expansion
reaches a fixed point without introducing a new smart tactic.

## Target selection

`TARGET` can be a sidecar, example project, examples directory, mdtest,
mdtests directory, or repository root. A repository-root audit covers both
`examples/` and `mdtests/`. `--claim`, `--changed-since`, and `--start-at`
narrow that target; their exact interaction and defaults are listed below.
For a sidecar with Click imports, the inventory contains only smart sites owned
by the selected entry module. Its imports resolve within its project root,
as under `click verify`. The retained session keeps imported interfaces
fixed while checking each rewritten local proof; audit the library path itself
to select library sites.

Expected-failure mdtests are excluded before runtime discovery or input
preparation. They contribute no audit sites, including when selected alone.
A mixed selection still audits its positive sources, and syntax or input
errors in a positive fixture fail the audit.

The inventory includes smart tactics inside ordinary `have` bodies, including
nested bodies and checked proof arms. A smart container owns its body: its
inner aliases count as one site. Audit and profile use the same source table
as location-based expansion.

A claim with no smart site can still rely on the implicit closer. It proves a bare simple tactic's open
requirement, such as a `step()`'s
precondition or a `fold`'s body fact. The inventory finds these claims by
verifying each source once and lists each as one `implicit closer` site, so
they are audited too. A source with no smart site that fails this verification
fails the audit; one with smart sites is reported by its session.

## Checks

A wholly selected claim is expanded once with all its smart sites. The
rewrite must contain no smart tactics and pass retained and cold verification.
Cold replay disables implicit solving inside the selected claim and its nested
proofs. It also rejects monitored discovery, including ambient search,
proposition search, and legacy fact transport. Neighboring claims and modeled
workers keep their ordinary verification policy. A selected claim that cold
replay did not visit fails the audit.

A cursor, site cap, or changed-source selection can select part of a claim.
Audit rewrites the selected sites together and checks that the emitted regions
contain only simple tactics. The rewritten unit then passes retained and cold
verification with unselected automation still available.

Each phase has a deterministic work budget. Replay uses the usual per-tactic
budgets and the input-sized work allowances of the checked operations that
define them. An allowance failure identifies the operation and its enclosing
tactic when available. Use the verifier's scaling tests to measure work across
multiple input and context sizes.

The verbose report shows original and rewritten cold work, the number of
lines containing written tactic tokens, and the selected proof's lines per
second. About 300 lines per second is acceptable and 700 is good. Audit
highlights a work increase above both twice the original and the configured
slack. These measurements are diagnostic. Phase time limits contain hung or
starved runs. The whole-run deadline interrupts phases cooperatively and leaves
the phase watchdog's configured time limit in place.

## Options and defaults

| Option | Default | Meaning |
| --- | ---: | --- |
| `--session-work-limit UNITS` | `100000000` | Budget each source's smart-site inventory, and each original-sidecar session initialization. |
| `--expansion-work-limit UNITS` | `50000000` | Budget the deterministic work of one expansion or re-expansion. |
| `--verification-work-limit UNITS` | `50000000` | Budget the deterministic work of one retained or cold proof-unit verification. |
| `--performance-slack UNITS` | `10000` | Set the minimum work increase to highlight in the report. |
| `--slow-site-limit UNITS` | `10000` | Deprecated alias for `--performance-slack`. |
| `--session-time-limit DURATION` | `10m` | Contain a hung inventory or session initialization. |
| `--discovery-time-limit DURATION` | `10m` | Compatibility alias for `--session-time-limit`. |
| `--expansion-time-limit DURATION` | `10m` | Contain a hung expansion or re-expansion. |
| `--verification-time-limit DURATION` | `10m` | Contain a hung proof-unit verification. |
| `--time-limit DURATION` | `10m` | Limit the whole audit, including inventory; print a resume cursor when sites are known. |
| `--start-at PATH:LINE:COLUMN` | none | Resume inclusively at a source location. |
| `--claim CLAIM` | all | Select an exact claim by its [label](expand.md#claim-labels), or `PATH:LINE[:COLUMN]`: the claim whose clause or proof covers that line of an audited sidecar or mdtest (Markdown lines), as `click expand --claim` resolves it, except that a line of a loop phase written in a `loop` tactic selects the proof that writes the tactic, whose sites include the phase's. A label shared by several audited files is ambiguous; a location names one. Repeat the option to select several claims. |
| `--changed-since REVISION` | none | Select claims affected since a Git revision. |
| `--verbose` | off | Include phase costs, proof size, and throughput for each claim batch. |
| `--keep-going` | off | Continue after failures instead of stopping at the first failure. |
| `--exclude PATH` | none | Leave out a proof container, or every one under a directory. Repeat the option for several. A path that matches nothing in the audited path is an error. |
| `--max-sites COUNT` | unlimited | Run a positive bounded number of sites and print the next cursor. |
| `-h`, `--help` | none | Print command help and exit successfully. |

Duplicate claim selection, a zero site count, an unknown claim, and an
ambiguous claim across sidecars are errors.

## Output and exit behavior

Passing progress is one row per claim. A claim failure prints a command for
that selection and an inclusive resume command for the larger run. A bounded
or timed-out run prints a resumable command with its selection and output mode. After inventory, its `--start-at` cursor retries the unfinished site
inclusively. If preparation is interrupted before sites are known, the summary
reports that no sites were audited and the command restarts the same selection,
retaining an existing cursor if one was supplied. The summary distinguishes
passing sites, site failures, claim failures, session failures, and incomplete
work.

The command exits with status 1 for any audit failure or exhausted hard limit.
The full audit runs in the nightly workflow and is a release check.

## Example

Audit all examples and mdtests, continuing long enough to collect independent
failures:

```console
click audit --keep-going .
```

## Related commands

Use [`click verify`](verify.md) for ordinary correctness and
[`click profile`](profile.md) for performance diagnosis. The
[auditing concept](../../concepts/audit.md) explains how audit extends the
checks performed by [`click expand`](expand.md).
