# Verifier design

This page divides the verifier into its parts and states what each part may
cost. Read it before proposing or reviewing a change to the verifier. A
proposal that adds work to the verifier names the part it changes and answers
the [design check](#design-check) below.

## Two parts: fast and slow

Every piece of the verifier is in one of two parts.

The **fast part** checks. It runs C one statement at a time, keeps the facts
of the current path, decides conditions, reads memory, tracks resources, and
applies simple tactics and certificates. Every proof pays its cost on every
step, and nothing can remove that cost later.

The **slow part** searches. It is the four smart tactics, `arithmetic`, `simp`,
`execute` (with its variant `execute_until`), and `auto`, and the search
helpers that fill an argument a tactic leaves out. Its cost is optional:
`click expand` replaces a slow-part tactic with the fast-part steps it chose,
and the expanded proof runs no search.

That difference sets the rules. A slow-part search can be expensive, because
an author who finds it slow can expand it away. A fast-part cost can't be
removed, so it has to stay small.

## The parts

| Part | What it does | Part of | Main code |
| --- | --- | --- | --- |
| Frontends | Parse, validate, and lower C, C++, Rust, and Surface Click | fast | `src/languages/`, `src/surface/{parser,names}.rs`, `src/surface/validation/`, `src/surface/lowering/` |
| Symbolic execution | Run statements, calls, and loops on a symbolic state | fast | `src/kernel/eval*`, `src/kernel/functions.rs`, `src/kernel/loops.rs`, `src/kernel/proof/execution.rs` |
| Fact store | Hold the path's facts in persistent indexes, with the equality closure and the difference graph | fast | `PureFactContext` in `src/kernel/assumptions.rs`, `src/kernel/equality_graph*`, `src/kernel/difference_graph.rs` |
| Condition decision | Decide one condition (order, overflow, equality, consistency) from the facts | fast | `PureFactContext::decide`, `src/kernel/assumptions/condition_reasoning/` |
| Memory | Snapshots, the memory derivation DAG, and load and store resolution | fast | `src/kernel/primitives/cell_store.rs`, `src/kernel/reasoning/memory_resolution.rs`, `src/kernel/memory_provenance.rs` |
| Resources | Ownership, views, loans, folds, and separation | fast | `src/kernel/primitives/resource_algebra.rs`, `src/kernel/resource_tracker/`, `src/kernel/loans.rs` |
| Simple tactics | Apply one checked step to a persistent proof state | fast | `src/kernel/proof/object.rs`, `src/surface/proof/proof_object/`, `src/surface/proof/checked_drivers/` |
| Certificates | Check explicit arithmetic certificates and contract claims | fast | `src/kernel/proof/{integer_arithmetic,signed_arithmetic,arithmetic_special}.rs`, `src/surface/proof_certificate.rs` |
| Termination | Plan recursion heights over the call graph, then check them | fast | `src/kernel/termination.rs` |
| Smart tactics | `arithmetic`, `simp`, `execute`, `auto` | slow | `src/surface/checking/{arithmetic_engine,simp,simplex}.rs`, `src/surface/proof/{smart_closures,smart_execution,solver_bridges}.rs` |
| Search helpers | Fill an elided premise, fact, resource instance, or guard | slow | `src/surface/planning/proposition_search.rs`, `src/surface/proof/fixed_state_proofs/` |
| Expansion and printing | Write a slow-part result as fast-part tactics, and print source | tools | `src/surface/expansion.rs`, `src/surface/printing.rs` |
| Tools and budgets | `profile`, `audit`, traces, work accounting, and budgets | tools | `src/bin/`, `src/instrumentation.rs` |

The kernel checks everything the fast part concludes, so a bug in the slow
part can lose a proof but can't prove something false. The tools decide
nothing.

## The fast-part rule

A fast-part operation does indexed lookups and work proportional to its
explicit input and the state it produces. It doesn't scan.

- **Input** is what the operation names: a tactic's written arguments, the C
  statement being executed, the condition being decided, and the definitions
  those name.
- **Output** is the state it adds: new facts, new paths, unfolded members, a
  certificate.
- **A lookup** reads an index by a key built from the input, such as the
  facts that mention a variable or the cells of one block.
- **A scan** reads a collection that grows with the program, the path, the
  facts, the snapshots, or the resources, and then keeps only the entries it
  needs. This rule has no exceptions: a fast-part operation doesn't scan even
  the facts "related" to its input unless an index hands them over by key.
  Following an index from entry to entry (a chain of order facts, say) is
  allowed when each step reads only entries filed under the current key and
  the walk reads each entry at most once.

Writing `N` for the size of the selected C, Click, and proof text, `q` for the
operation's input, and `d` for its output, one operation costs
`O((q + d) polylog N)`, and a project written entirely in simple tactics
verifies in `O((N + D) polylog N)`, where `D` is semantic output such as
enumerated paths. [Verification efficiency](verification-efficiency.md#complexity-contract)
gives the full contract.

The condition decision is in the fast part. Simple tactics such as `fold` and
`step` call it to check a premise, and expansion can't remove it, so it
follows the same rule. Its per-query fuel is a safety net that stops a
runaway decision, not a license to scan.

Operations in the fast part that scan today are listed, with the options for
each, in
the "Fast-part scans" section of [the smart-tactics issue](https://github.com/clicklang/click/blob/master/issues/smart-tactics.md).

## The slow-part rule

A slow-part search may scan, try alternatives, and recurse, under three
conditions:

1. **It is bounded.** It runs under a deterministic work budget and fails
   promptly, with a bounded diagnostic, when the budget runs out.
2. **It is expandable.** `click expand` writes what it found as fast-part
   tactics, or as the same tactic with its elided argument written out.
   After expansion no search runs.
3. **It is checked.** It advances the proof only through fast-part
   operations, so the kernel checks everything it concludes.

A search that can't be written out as explicit tactics isn't allowed in the
slow part either: then there's no way to remove its cost, which makes it fast
part, and fast part may not search. [Smart and simple
tactics](../concepts/smart-and-simple-tactics.md) defines the tactic classes
and the target set of four smart tactics.

## Design check

Answer these before proposing a verifier change that adds work.

1. **Which part does it change?** Name it from the table above.
2. **Fast or slow?** If it adds reasoning to a fast part, ask first whether
   it could be a slow-part search instead: a new strategy in `simp` or
   `auto`, or a helper for an argument a tactic already takes. Put it there
   unless every proof needs it on every step.
3. **If fast:** which index serves each read, and what is the key? Which
   scaling test grows both unrelated and related input (more facts about
   other values, and a longer chain of facts about this one) and shows the
   work stays near-linear? "It's cheap" and "the corpus didn't get slower"
   don't answer this.
4. **If slow:** what does `click expand` write in its place, and what
   explicit syntax lets an author write that result without the search? If
   that syntax doesn't exist, adding it is part of the change.
5. **What does it fail with?** A slow-part miss names what wasn't found and
   how to supply it. A fast-part refusal names the rule it checked.

A change that can't answer question 3 or question 4 doesn't go in.

## Vocabulary

Proposals often name a mechanism rather than a part. These are the parts the
common mechanism names belong to.

| Term | What it is | Part |
| --- | --- | --- |
| condition decision, `decide` | Decides one condition from the facts | Condition decision (fast) |
| difference graph | Index of `x - y <= c` bounds between values | Fact store (fast) |
| equality graph, equality closure | Index of which terms are known equal | Fact store (fast) |
| order walk, order path | Follows order facts from one term to another inside a decision | Condition decision (fast) |
| overflow intervals, bounds | Value ranges read to decide overflow | Condition decision (fast) |
| memory resolution | Finds the value a load reads across stores | Memory (fast) |
| memory DAG, snapshot, cell store | How memory states and their cells are stored and related | Memory (fast) |
| DAG bridging | Relating a load at one snapshot to cells of an earlier one | Memory (fast) |
| carriers, compositions, separation | How owned resources and their disjointness are represented | Resources (fast) |
| fold, unfold, views, loans | Building, opening, and borrowing resources | Resources (fast) |
| proof object, proof step | The persistent proof state and one checked change to it | Simple tactics (fast) |
| certificate | An explicit derivation the kernel checks without search | Certificates (fast) |
| planner (signed, `Integer` affine, special) | Chooses an arithmetic certificate | Smart tactics (slow) |
| solver, simplex, refutation | `auto`'s linear-arithmetic search | Smart tactics (slow) |
| rewrite search, equality chain | `auto`'s search for rewrites that close a goal | Smart tactics (slow) |
| premise selection, connected premises | Choosing which facts a tactic uses | Search helpers (slow) |
| transport planner | Choosing the facts a bare `transport` carries | Search helpers (slow) |
| theorem premise cascade | Finding the premises of a bare `apply` | Search helpers (slow) |

## Where the details are

- [Verification efficiency](verification-efficiency.md): the complexity
  contract, representation requirements, regression policy, and notes on
  how specific operations meet the contract.
- [Smart and simple tactics](../concepts/smart-and-simple-tactics.md): the
  tactic classes.
- [Testing](testing.md): how to write a scaling test and measure deterministic
  work.
- [Architecture](architecture.md) and [Kernel](kernel.md): the code layout.
