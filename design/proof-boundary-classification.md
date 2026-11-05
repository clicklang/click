# Proof boundary classification

Source audit of `6e59bda97` (PR #2459), following the proof/search/driver split.
This classifies all 19 `mixed` and 15 `operation-to-driver` reference records in
`build_support/proof_search_edges.tsv`. It changes no verifier behavior or
machine inventory. A classified call is not a complexity proof for its callee.
No new scaling measurements were made for this audit.

## Current migration status

The have prerequisite callback described below has been extracted:
`Proof::begin_have` now reports requirements without scheduling their proofs;
`ProofDriver::open_have` owns the ordinary obligation-solving orchestration.
The enforced inventory now contains 14 operation-to-driver records. The tables
below retain their explicitly identified audit snapshot; focusing and resource
scope completion still have the other two obligation callbacks. This extraction
does not resolve the separate cost of separation observation during have setup.

## Findings

The old categories describe code placement, not the reason search runs. Most
ambiguous references are expected orchestration or discovery helpers. Three
other concerns need separate treatment: operations that implicitly solve before
returning, declaration validation that searches outside proof scripts, and
failure diagnostics that execute more operations.

The known direct operation/search dependencies remain: this classification does
not eliminate the seven kernel bridges, their 22 caller records, or the 14
Surface operation/search records. In particular, explicit premises are not an
explicit derivation: `transport(...) using {...}` is classified Simple in
`src/surface.rs`, but its application can still call `derive_atomic_proposition`.
Bare `transport(...)`, by contrast, is classified Smart and may discover evidence.
Expanding the latter into the former is not by itself a search-free guarantee.
`transport_certificate` is a different operation and must be audited separately.

## The 19 mixed reference records

Paths below are relative to `src/surface/`.

| Caller | Records | Classification and source evidence |
| --- | ---: | --- |
| `check_initialization_body` | 2 | Driver dispatch. In `proof/execution_planning/loop_planning.rs`, omitted/written solve calls the solver; a written script calls the script interpreter. |
| `verify_loop_initialization_pure_proof` | 1 | Driver dispatch. Executes explicit phase-helper unfolds and `have` bodies. |
| `verify_one_loop_preservation_proof` | 2 | Driver dispatch. Invariant search is under `region_solve.is_some()`; retained bodies take a different route. Also prepares invariant obligations through the driver. The surrounding state-join/revalidation work still needs its own cost audit. |
| `check_direct_pure_goal_with_proof` | 2 | Driver dispatch. Discharges entry obligations, then runs ordinary solve for an omitted or written solver proof. |
| `check_pure_script_with_proof` | 1 | Driver dispatch. Runs written proof steps and discharges outstanding entry obligations. |
| `check_pure_structural_induction` | 1 | Driver dispatch. Interprets the prepared explicit induction-case scripts. This says nothing about binder freshening or preparation cost. |
| `verify_contract_refinement_theorem` | 1 | Driver dispatch. Executes the refinement proof script. |
| `verify_theorem_ensure` | 1 | Driver dispatch. The inventoried calls discharge declaration-entry obligations, including trusted-theorem declaration paths. |
| `try_steps` | 1 | Search support. `proof/attempt.rs` tries candidate steps under an attempt budget; production callers are in `smart_closures/search.rs`. |
| `execute_enum_match_group` | 1 | Search support misplaced on `Proof`. Reached through `execute_enum_match_to_exit` from `proof_object/execution_joins/search.rs`; it searches each enum arm to exit. It is not the expanded-arm interpreter. |
| `Carried::establish` | 2 | Search support. Called from `selected_arithmetic/search.rs`; constructs selected arithmetic bridges, including proving missing bounds. |
| `plan_explicit_loadability_transport` | 1 | Search support. `surface_certificates.rs` selects/minimizes premises and returns written tactics for solve. Here “explicit” describes the output, not the planner's cost. |
| `plan_explicit_predecessor_upper_bound` | 1 | Search support. Used by solve directly and by the recorded signed-order planner; may plan equality rewrites. |
| `plan_explicit_fact_transport` | 1 | Smart transport planner. Reached from smart execution and the bare-transport adapters on `Proof`; builds contexts from available facts/effects and tests derivability. Its output is an explicit `TransportUsing` operation, whose separate remaining search is not excused by this classification. |
| `segment_contains_pointer` | 1 | Declaration-validation search. `checking/segments.rs` calls `ProofSearch::proves` for bounds; the production caller is resource-definition read-coverage validation in `validation/definition_validation.rs`. This is not ordinary implicit solve on a user proof obligation. Determine the declaration-input cost bound and how expensive reasoning can be replaced by explicit evidence. |

Totals: 11 interpreter/obligation-dispatch records, 7 discovery/support records
(including bare transport), and 1 declaration-validation search record.
These roles should eventually replace the ambiguous labels after review; this
audit deliberately does not silently regenerate the enforced inventory.

## The 15 operation-to-driver reference records

Methods below are on `Proof` except `ProofScope::join_inner`.

| Caller | Classification and action |
| --- | --- |
| `apply_execution_branch_within` | Nested-script interpretation: dispatches the written arm steps. Move orchestration off the primitive interface; splitting, focusing and joining remain operations. |
| `apply_execution_if_within` | Nested-script interpretation: dispatches then/else scripts. Same separation. |
| `apply_focused_expanded_execution_arm` | Expanded-script interpretation: dispatches the retained arm with `expanded=true`. That flag is not proof that every transitively called helper avoids search. |
| `begin_have_spelled` | Hidden obligation dispatch: unless implicit solving is disabled, calls `with_proved_lowering_requirements`, which probes, solves, and reruns the operation. Return the obligations to the outer driver instead. |
| `focus_bare_kernel_claim_goal` | Hidden obligation dispatch: calls `discharge_entry_requirements` before returning the focused goal. The resulting proof prefix is retained, but focusing is not a purely fast API today. |
| `ProofScope::join_inner` | Hidden obligation dispatch in the resource-open case: calls `close_scope_with_body_fact_proof`; this may execute the written closing proof or invoke ordinary solve. Split raw scope completion from scheduling its required proof. |
| `plan_invariant_bundle_closure` | Search/orchestration adapter on the wrong interface: forwards to the driver planner and records the missed member. Used by invariant-closing orchestration. |
| `solve_open_for_missing_resource` | Search helper on the wrong interface: selects a resource to unfold, called from smart retry. |
| `unsigned_strict_fact` | Search helper on the wrong interface: called from smart closures and may prove a reversed inequality using arithmetic. |
| `apply_signed_definedness_certificate` | Search-support adapter: called by signed-definedness search; constructs an explicit arithmetic certificate and dispatches it. Separate the generator from direct certificate application; do not count this edge alone as a hidden ambient scan. |
| `apply_planned_fact_transport_inner` | Bare-transport search adapter, not a primitive despite its location. Plans premises, then dispatches `TransportUsing`. |
| `apply_planned_outcome_fact_transport` | The same bare-transport adapter at a completed execution outcome. |
| `apply_fast_simple_step` | Compatibility adapter: folds re-enter `apply_step` under `without_implicit_solve`. This suppresses implicit solving, not all discovery. Extract the direct fold operation rather than granting general driver access. |
| `exclude_execution_match_arm_after_bridge` | Dispatch adapter for a specific explicit contradiction step, with source-site/certificate recording. No search selection at this call; use direct operation plus recording instead of the general driver. |
| `unfinished_callback_diagnostic` | Failure-path execution. On an incomplete script, speculatively runs up to six ordinary driver steps to improve the error. Each can invoke implicit solving. Six steps is not a work bound; this is ordinary error reporting, not opt-in tracing. |

Totals: 3 nested-script interpreters, 3 implicit-obligation callbacks, 6
search/support adapters, 2 specific-operation dispatch adapters, and 1 diagnostic
execution callback. Some categories overlap semantically; each record is counted
once here according to why this particular driver call exists.

## Why accidental search remains possible

1. `kernel::search::ProofSearch<P>` is a namespace with static associated
   functions. `proves(context, goal)` needs no search-access argument. Merely
   moving a method here does not make it unavailable to operations.
2. Every Surface `Proof` and `ProofScope` implements `DriveProof`; `.driver()`
   can be obtained inside operation implementations. This allows the indirect
   route operation -> driver -> solve, including obligation callbacks above.
3. `without_implicit_solve` gates automatic solving at selected sites. It does
   not prohibit direct `ProofSearch` calls or legacy search wrappers. Passing
   cold replay under it is useful evidence, not the full no-search condition.
4. `SearchPermission` protects selected ambient enumeration interfaces. It
   is not required by every search entry point or every potentially growing
   collection operation. Its current scope is narrower than the desired rule.
5. The build inventory recognizes registered names, method references and macro
   tokens. It is lexical, not a transitive/type-resolved call graph. Driver
   classification is largely by placement, so code added inside a driver can
   be inventoried without proving that it is legitimate search dispatch.
6. Work can be bad without calling any search API: rebuilding contexts, copying
   terms, validating a result already constructed, traversing history, and
   enumerating growing index buckets. Source guards alone cannot detect this.
7. Setup and error reporting need their own cost contracts. Moving expensive
   work before the first step or after failure does not establish the overall
   fast-proof guarantee, and there may be no tactic the user can expand there.

## Recommended next boundary, for design review

Keep the existing persistent proof state and direct successor construction.
No second checker or producer/rechecker layer is needed.

- Primitive operations return a successor or outstanding obligations. They
  cannot acquire a driver or invoke a proof script. The outer driver executes
  supplied proofs, invokes solve when omitted, and resumes the operation.
  Start with `begin_have_spelled`, focusing, and resource-scope completion;
  move the identified script/search adapters out of the primitive interface.
- Make search access explicit at every discovery entry, including compatibility
  wrappers: a driver-owned access capability passed to search, never stored in
  the proof state or handed to primitive operations. Restrict its construction
  to reviewed smart/implicit dispatch, not arbitrary driver methods. The
  existing partial `SearchPermission` mechanism is a starting point, not
  evidence this is already enforced.
- Add a strict replay/operation guard against **all** registered discovery,
  not just implicit solve. During migration, name existing exceptions and make
  new ones fail. A primitive invoked by a search still runs under the fast
  restriction; being inside solve must not exempt its internal work. The guard
  checks access policy at execution time; it does not replay or revalidate a
  proof result.
- Keep deterministic complete-operation scaling tests for the work no search
  boundary can detect. Fix explicit input/state delta, grow unrelated state,
  and cover successful, failing, cold, repeated and persistent-branch cases.
- Give normal diagnostic work a bounded interface over retained error evidence.
  Treat further speculative execution as an explicitly requested diagnostic
  search rather than work silently performed to report a fast failure.

The immediate implementation proposal should therefore establish and test one
non-reentrant primitive boundary, rather than starting another unrelated scan
removal. The hidden lowering-obligation callback in `begin_have_spelled` is a
concrete first slice. The remaining legacy searches then become named migration
exceptions to remove with the red-test/design/build cycle. Definition-validation
proof support and a general change to diagnostic behavior need separate design
review; they are findings here, not implementation authorization.
