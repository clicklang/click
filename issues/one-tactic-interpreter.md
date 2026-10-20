# One source-tactic interpreter for every proof context

Priority: P1.

Soundness: not soundness. Every route still applies checked `Proof`
transitions, so a context that handles a tactic differently refuses a proof
or expands it differently. It does not accept a false claim. The cost is
completeness, expansion fidelity and maintainability. A tactic means slightly
different things in different places, and adding one tactic touches about
fifteen files.

P1 by user direction (2026-10-15).

## Current state and violated invariant

`design/proof-object-api.md` finished the move to one immutable checked
`Proof`. It forbids "one special transaction driver per smart tactic or goal
kind". The source tactics written in a `.click` file are still interpreted by
a separate hand-written driver in each proof context:

- the linear execution continuation (`advance_checked_linear_continuation`),
  focused execution arms (`advance_focused_execution_arm`) and linear `open`
  scopes (`advance_linear_open_scope`) in
  `src/surface/proof/checked_drivers/proof_execution.rs`;
- tactics after execution, through the separate `PostExecutionTactic` enum
  (`src/surface/proof/execution_state.rs`), in `finish_ordered_proof`
  (`src/surface/proof/claim_proofs.rs`), which is one function of about 3,900
  lines;
- explicit scripts inside smart search (`try_authoritative_linear_script` in
  `src/surface/proof/smart_closures.rs`), loop initialization
  (`execution_planning/loop_planning.rs`), pure theorems and claims
  (`verification.rs`).

The copies have drifted:

- A written `transport` falls back to `apply_planned_fact_transport` in the
  linear driver. A focused execution arm declines the same tactic.
- A nested `have` miss is an error through `solve_nested_have`, but a
  decline (`LinearScriptDecline::Step`) in the script runner.
- `simp` in an execution arm is refused, while a `preserve` body has its own
  `simp` handler.
- `smart execute` runs `try_execute_to_exit` in the linear driver and
  `try_focused_execute_to_exit_within` in an arm.

Representation is mirrored as well:

- the tactic exists as `ProofTactic` (`src/surface.rs`), `ProofStep`,
  `PostExecutionTactic` and `FlatTactic` (`src/surface/expansion.rs`);
- there are four `ProofTactic` → `ProofStep` converters (`explicit_linear_step`,
  `linear_execution_proof_step`, `arm_proof_step`,
  `ProofCertificate::from_proof_tactics`) plus `flat_post_execution_tactic`;
- recursion over a control tactic's children is written out by hand in each
  traversal.

Expansion also records what ran apart from the checked certificate.
`record_post_execution_surface_tactic` (18 call sites) and
`record_proof_site_tactic_expansion` (15) push surface tactics by hand next to
`Proof::certificate_since`. Neighbouring arms disagree about which one they
use. Drivers decline through thread-local state (`DRIVER_DECLINES`,
`REGION_DEPTH_DECLINED`, `SHORT_OF_EXIT_DECLINED`, `DECLINED_OPERATION`), and
the final diagnostic is rebuilt from it.

The invariant: one function applies a written source tactic to a proof
context. A context (pure goal, execution frontier, execution arm, `open`
scope, post-execution outcome path, loop body) differs only in the `Proof`
state it supplies and in which tactics it admits, and admission is a declared
table, not a separate code path. Expansion prints what checking recorded, from
one source of truth.

## Case splits

Proof `if`, `cases` and `match` follow one rule in every context
(`docs/reference/tactics/index.md`, "Case splits"). Each arm runs once.
With tactics written after the split, the live arms rejoin with the facts
every arm proved, or the split is refused. An arm that reaches function exit
is a finished path, and the closer that ends the proof closes its goals.
After execution a split that forks outcome paths does not rejoin, so tactics
after it are refused.

Two differences remain for `match` after execution:

- A `match` at function exit splits once at the exit frontier, on the facts
  every outcome path shares, through the frontier `match` driver. `if` and
  `cases` decide each outcome path: a path whose facts decide the case runs
  only its arm, and only an undecided path forks. So on a path whose facts
  rule out a constructor, that arm still runs. Closing it needs a deferred
  `match` that issues the kernel's constructor partition against each
  path's facts, an n-way `OutcomeEvidenceFork`, and n-way certificate
  synthesis in `synthesize_surface_paths`.
- A `match` nested in the arm of an `if` or `cases` after execution is
  deferred and decided per path through the n-way `OutcomeEvidenceFork`,
  except with `ensuring` or an arm that is a lone `contradiction`, which
  `deferred_post_execution_region` still declines. The top-level `match`
  should move onto the same deferred path.

Both are easier once claims are goals held by the `Proof`, so that the three
splits share one post-execution implementation.

## Intended regression

Add mdtests that write the same tactic in each context where the language
admits it and expect the same verdict and the same expansion. Cover a written
`transport`, a nested `have` whose body misses, `simp`, and `smart execute`
at the linear frontier, in a focused arm, in an `open` scope and after
execution. Each drift above becomes either an agreeing pair or a documented
refusal with a diagnostic that names the context. Keep every existing
expansion round-trip regression.

## Acceptance criteria

- One `apply_source_tactic(context, tactic)` serves every context listed
  above. What each context admits is declared in one place, and a refusal
  names the context.
- `PostExecutionTactic` and the duplicate step converters are removed, or each
  remaining one is justified in this file. Control tactics expose their
  children through one visitor.
- `finish_ordered_proof` and the `advance_*` drivers shrink to the
  context-specific setup and teardown.
- Expansion derives its output from the checked certificate. No hand-pushed
  surface-tactic record runs alongside it.
- Driver declines are typed return values, not thread-local state.
- `docs/reference/tactics/index.md` states any remaining context-specific
  behavior.
- The gate, the nightly corpus and the expansion audit show no verdict
  changes. Any change that does appear is filed and explained.
