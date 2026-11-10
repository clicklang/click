# Separate proof operations from proof search

Status: proof/search split, explicit proof driver, and shared implicit/explicit solver implemented.
The next step is to remove the inventoried operation-to-search dependencies
one at a time. The general fast-operation guarantee is not established yet.

## Design check

- **Parts:** proof operations, discovery, proof-script driver, persistent state.
- **Boundary:** explicit operations remain on `kernel::proof::ProofObject` and
  its Surface `Proof` wrapper; discovery is exposed through `kernel::search::ProofSearch`.
- **Cost:** the interface split preserves operation costs. The shared solver
  includes the former implicit zero-witness attempt, entry-witness transport,
  and return-resource folding;
  these remain expandable search, with existing budgets.
  The eventual operation bound is selected input and necessary state delta,
  up to indexing factors; ambient buckets and history are not explicit input.
- **Result:** search uses the existing operations and persistent successors.
  There is no second proof state, proof conversion or new validation pass.
- **Lowering/refusal:** syntax and obligation generation are unchanged.
  An omitted obligation proof and written `solve()` use the same strategies;
  explicit solve can now prove the former implicit-only zero-witness case.

## Implemented split

`ProofObject` remains the authority for semantic successors. `ProofSearch<P>`
is a stateless associated-function interface over an existing context `P`.
For example, `ProofSearch::derive_proposition(&facts, &goal)` searches over
kernel facts, while a Surface specialization can use the same interface to
select and spell a sequence of source proof operations. There is no new
runtime session, allocation, copied proof or permission check.

Both interfaces belong to the kernel. Implementation placement follows the
inputs each method needs:

- `kernel/search/proposition_search.rs`: semantic proposition discovery,
  formerly a trait supplied by Surface planning.
- `kernel/search/permission.rs`: the existing enumeration capability, with
  its existing construction semantics unchanged.
- `kernel/**/legacy_search.rs`: extracted traversals beside the private state
  they inspect. Existing entry points forward to `ProofSearch` unchanged.
- `surface/proof/**/search.rs`: discovery that needs Click source terms,
  spelling or expansion records, implemented on `ProofSearch<Proof<'a>>`.
- `surface/planning/solve.rs`: existing certificate planning support.

The explicit Surface `Proof` interface no longer owns the extracted discovery
methods. Its remaining calls to search are visible in the dependency inventory.
`ProofScope` search forwarding adapters now belong to `ProofDriver<ProofScope>`. Direct helpers such as indexed fact lookup and
retrieving the retained spelling map stay outside the search interface.

The existing `PropositionDerivation` representation and its checking lifecycle
are unchanged. Moving its discovery code does not endorse producer/checker
revalidation as a design for new operations.

## Driver and obligations

`surface::proof::driver::ProofDriver` borrows a `Proof` or `ProofScope`. It
interprets source proof steps, nested scripts, theorem applications and closure
bodies, choosing explicit operations or `ProofSearch` at each frontier. This
is one interpreter, not separate fast and slow passes. `proof.driver()` borrows
the existing persistent state without allocating or copying it.

The implementations live in `surface/proof/driver/`. Existing helper modules
mount those files as private child modules to retain helper visibility. Claims
and execution orchestration are also housed there, with their existing logical
module names preserved. The kernel's semantic `ProofObject` and `ProofSearch`
remain kernel interfaces; this source interpreter belongs in Surface because
it consumes parsed Click proofs, source locations and expansion records.

For statement obligations:

1. `Proof::prepare_step` runs the existing operation under its obligation probe,
   returning the existing conditional candidate and recorded requirements.
2. The driver proves those requirements at the original frontier, using the
   supplied `by`/`requires` blocks or implicit search when no block was written.
3. `Proof::finish_prepared_step` resumes with the proved requirements using the
   existing candidate/retry behavior. The candidate cannot prove its own inputs.

Obligation generation is intended to be fast; implicit solving is legitimately
slow and expandable. An omitted obligation proof invokes the same
`ProofSearch::try_solve_closure` entry point as written `solve()`. The driver
provides no private witness heuristic, extra premise list or caller-requirement
shortcut. Such strategies belong in the shared solver. The implicit tail
schedules the remaining C and outstanding goals; it is not another solver. Step preparation now retains required prerequisites even when already known,
and fold body facts use the same obligation driver. The driver handles every
unwritten slot through ordinary solve. The raw fold operation no longer
re-enters the driver. Failed statement preparations and folds still use the
existing recovery retry after their obligations are proved.

## Dependency inventory and enforcement

[`build_support/proof_search_edges.tsv`](../build_support/proof_search_edges.tsv)
is the frozen production reference inventory. Columns are source path, caller
role, owner/function, search or driver target and number of references. Repeated calls
from one function to one target share a record. It is a lexical reference
inventory, not a type-resolved or transitive Rust call graph.

Roles distinguish the work remaining:

| Role | Meaning |
| --- | --- |
| `legacy-bridge` | Seven preserved kernel forwarding boundaries into extracted traversals. |
| `legacy-caller` | Kernel dependencies on those old entry points; these expose propagation beyond the seven bridges. |
| `operation` | Source operation, transport, validation or transition construction still calls discovery. |
| `driver` | Explicit proof interpretation, including legitimate implicit obligation solving. |
| `operation-to-driver` | Remaining proof-operation calls into orchestration; inspect their transitive behavior. |
| `dispatch` | Source drivers explicitly select a smart tactic or implicit closing. |
| `presentation` | Spelling and trace helpers depend on discovery helpers. Audit independently of semantic steps. |
| `search` | Calls made within the extracted search interface or planning modules. |
| `mixed` | Drivers and auxiliary planners; semantic roles are recorded in the caller audit. |
| `import` | Named import, not a runtime invocation. |

The current inventory after exact-goal solve selection contains 613 records: 7 legacy bridges, 22 kernel callers,
14 Surface operation dependencies, 8 operation-to-driver dependencies,
110 driver records, 1 other dispatch record, 6 presentation records,
424 search-internal records, 19 mixed records and 2 imports. These are reference
records, not individual invocation counts or independent performance defects.

Do not add all these rows and call the result a count of slow bugs. Several
callers reach the same traversal; dispatch and search-to-search calls are
expected. The `operation`, `operation-to-driver` and legacy rows are the migration list;
`mixed` rows have caller-level roles in the linked audit; classification does
not certify their callees as fast. Four of the operation records belong to explicit tactic/theorem handlers now implemented
on `ProofDriver`: moving dispatch must not hide those search dependencies or
reclassify them as legitimate implicit solving. Driver placement alone is not
an efficiency guarantee.

Seven kernel bridges preserve these implementations:

| Existing entry point | `ProofSearch` implementation | Ambient work to resolve |
| --- | --- | --- |
| `memory_range_aliases` | `loan_aliases` | Pointer aliases used by loan queries. |
| `permits_memory_access_with_assumptions` | `loan_access` | Write permission, including symbolic protected ranges. |
| `owned_validity_candidates` | `ownership_validity_candidates` | Candidate owners for composition validity. |
| `memory_ranges_proven_overlapping_with_separation` | `ownership_overlap` | Alias-pair overlap discovery. |
| `pointers_distinct_by_owned_anchors` | `owned_anchor_distinctness` | Equality components and ownership compositions. |
| `compositions_only` | `composition_context` | Ambient composition context reconstruction. |
| `call_kept_ownership` | `call_frame` | Residual caller resources and composite families. |

`build_support/proof_search_boundary.rs`, invoked by the normal build boundary
check, rejects new references to the registered search entry points and new
unclassified `ProofSearch` methods. It also rejects returning a registered
search method to `Proof`. It also registers the driver methods, rejects moving
them back to `Proof`/`ProofScope`, and inventories `.driver()` acquisition so
new operation-to-driver dependencies require explicit review. Tests pin the exact inventory, including deletions,
and exercise direct calls, function references, type aliases and macro tokens.
Changing the inventory is a reviewable architecture change, not an automatic
regeneration to make the build pass.

This source guard does not establish complexity. It cannot discover a new
inline loop, resolve arbitrary macro-generated calls, or prove an arbitrary
helper fast. The existing operation audit and scaling tests remain necessary.
The separate target list includes compatibility entry points so a caller cannot
hide an existing search merely by using the old wrapper.

## Have prerequisite boundary

`Proof::begin_have` opens a nested goal or reports ordinary lowering
requirements; it does not acquire a driver or schedule their proofs.
`ProofDriver::open_have` (and its source-proof adapters) owns the existing
lowering-obligation probe, invokes the shared obligation solver when needed,
and opens the scope with the resulting facts. Strict replay takes the direct
operation path. No new obligation format or proof rechecker is introduced.
The existing probe/retry behavior is preserved; this change does not claim to
remove repeated preparation or the separate separation-observation costs.

The source boundary rejects driver and registered search references inside
`begin_have`. The primitive regression leaves implicit solving enabled and
requires raw opening to report a prerequisite; driver opening succeeds and
retains the prerequisite proof. Scoped-conversion expansion replays with
implicit solving disabled. Other operation-to-driver records remain pending.

## Contract-claim prerequisite boundary

`Proof::begin_contract_claim` opens an already-lowered claim or reports its
missing definedness obligations through the ordinary obligation channel.
`ProofDriver::open_contract_claim` imports the claim's lowering facts and
schedules prerequisite proofs. Its `open_contract_claim_without_lowering_facts`
adapter uses the existing facts instead. Both retain prerequisite certificates
before the claim's own steps, preserving expansion and strict replay.
The source guard prohibits direct driver/search references in the primitive.
Claim lowering, goal transformations, and state preparation are unchanged.

## Resource-scope completion boundary

`ProofScope::join` closes directly or reports the missing resource-body fact
through the ordinary obligation channel. It cannot call the driver or search.
`ProofDriver::complete_scope` owns written closing proofs and omitted ordinary
solve through the existing `close_scope_with_body_fact_proof` orchestration.
It retains the resulting proof as the scope's `by` for expansion. Nested opens
use `complete_nested_scope` before incorporating the direct checked successor.
Function-exit closes keep their existing deferred driver route. Superfluous,
incorrect, and missing explicit closing proofs keep their existing refusals.

## Branch interpretation boundary

`ProofDriver::apply_execution_if_within`, `apply_execution_branch_within`, and
`apply_focused_expanded_execution_arm` interpret arm scripts between the existing
proof-object split, focus and join operations. `apply_expanded_execution_if` is
also a driver entry point, including inside resource scopes. The former
`Proof::apply_execution_if_with` callback API is removed: proof-level cases now
use the same explicit split/focus/drive/join sequence in the driver. C-branch
entry checks, infeasible-arm refusals, parent continuations and terminal joins
retain their existing rules and exact checked histories. There is no second
checker or rebuilt proof state.

## Detailed caller classification

The [caller audit](proof-boundary-classification.md) classifies the current 19 mixed and
8 operation-to-driver records by why they invoke search or interpretation.
It distinguishes expected dispatch from hidden obligation callbacks, declaration
validation, diagnostic execution, and the remaining primitive search dependencies.
The proposed enforcement changes are for design review; no behavior changes or
new scaling measurements accompany that classification.

## Next step

For each operation dependency: reproduce its ambient cost with a red scaling
test, discuss the explicit rule or indexed representation, then replace the
search and repair proofs. Preserve the C program, contracts and safety refusals.
Remove the corresponding inventory records as the dependency disappears.
Start with loan permission through an actual write, separating alias growth
from symbolic-loan growth; the [operation audit](../roadmap/smart-tactics.md)
retains the other candidates and coverage gaps.

The intended end condition remains: an expanded proof executes through proof
operations without accessing `ProofSearch` or a legacy slow operation. This
refactor deliberately adds no strict runtime mode and does not claim that end
condition. Session capabilities, stricter state views and expansion enforcement
can be designed when needed; they are not prerequisites of this initial split.
