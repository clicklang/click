# Separate proof operations from proof search

Status: step 1 implemented as a behavior-preserving interface refactor.
The next step is to remove the inventoried operation-to-search dependencies
one at a time. The general fast-operation guarantee is not established yet.

## Design check

- **Parts:** proof operations, discovery, source adapters, persistent state.
- **Boundary:** explicit operations remain on `kernel::proof::ProofObject` and
  its Surface `Proof` wrapper; discovery is exposed through `kernel::search::ProofSearch`.
- **Cost:** this refactor does not change algorithms, indexes, budgets or costs.
  The eventual operation bound is selected input and necessary state delta,
  up to indexing factors; ambient buckets and history are not explicit input.
- **Result:** search uses the existing operations and persistent successors.
  There is no second proof state, proof conversion or new validation pass.
- **Lowering/refusal:** no changes to syntax, lowering, obligations, proof
  acceptance, diagnostics or search refusal policy are intended.

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
`ProofScope` still has search forwarding adapters; these are recorded separately
from primitive operations. Direct helpers such as indexed fact lookup and
retrieving the retained spelling map stay outside the search interface.

The existing `PropositionDerivation` representation and its checking lifecycle
are unchanged. Moving its discovery code does not endorse producer/checker
revalidation as a design for new operations.

## Dependency inventory and enforcement

[`build_support/proof_search_edges.tsv`](../build_support/proof_search_edges.tsv)
is the frozen production reference inventory. Columns are source path, caller
role, owner/function, search target and number of references. Repeated calls
from one function to one target share a record. It is a lexical reference
inventory, not a type-resolved or transitive Rust call graph.

Roles distinguish the work remaining:

| Role | Meaning |
| --- | --- |
| `legacy-bridge` | Seven preserved kernel forwarding boundaries into extracted traversals. |
| `legacy-caller` | Kernel dependencies on those old entry points; these expose propagation beyond the seven bridges. |
| `operation` | Source operation, transport, validation or transition construction still calls discovery. |
| `scope-adapter` | Existing scope wrappers forward explicit search requests. |
| `dispatch` | Source drivers explicitly select a smart tactic or implicit closing. |
| `presentation` | Spelling and trace helpers depend on discovery helpers. Audit independently of semantic steps. |
| `search` | Calls made within the extracted search interface or planning modules. |
| `mixed` | Mixed drivers and auxiliary planners still requiring caller-level classification. |
| `import` | Named import, not a runtime invocation. |

The initial inventory contains 439 records: 7 legacy bridges, 22 kernel callers
of those bridges, 14 Surface operation dependencies, 16 scope adapters,
13 dispatch dependencies, 6 presentation dependencies, 338 search-internal
records, 21 mixed records and 2 imports. These are reference records, not
individual invocation counts or independent performance defects.

Do not add all these rows and call the result a count of slow bugs. Several
callers reach the same traversal; dispatch and search-to-search calls are
expected. The `operation` and legacy rows are the concrete migration list;
`mixed` rows are explicitly unresolved, not silently declared fast.

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
search method to `Proof`. Tests pin the exact inventory, including deletions,
and exercise direct calls, function references, type aliases and macro tokens.
Changing the inventory is a reviewable architecture change, not an automatic
regeneration to make the build pass.

This source guard does not establish complexity. It cannot discover a new
inline loop, resolve arbitrary macro-generated calls, or prove an arbitrary
helper fast. The existing operation audit and scaling tests remain necessary.
The separate target list includes compatibility entry points so a caller cannot
hide an existing search merely by using the old wrapper.

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
