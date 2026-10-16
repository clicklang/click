# One kernel statement executor for both execution judgments

Priority: P1.

Soundness: soundness-adjacent. No false acceptance is known. The trusted
kernel has two hand-maintained implementations of statement and function
execution, one for each execution judgment, and they already differ in ways
the judgments do not explain. A reviewer of the trusted base has to check
both, and a fix applied to one is easy to miss in the other.

P1 by user direction (2026-10-15).

## Current state and violated invariant

`docs/internals/kernel.md` (execution semantics) deliberately keeps two
propositions apart. `CStatementExecutes`/`CFunctionExecutes` describe concrete
operational outcomes. `CStatementVerifies`/`CFunctionVerifies` describe
abstract branches admitted under loop and function rules, including the
`VerificationDiverges` marker. `CExecutionSemantics` already carries the call
and loop mode as data. Despite that, each judgment has its own driver:

- statements: `execute_c_statement_paths` (`src/kernel/eval/statements.rs`)
  and `execute_c_statement_verification_paths` (`src/kernel/loops.rs`, though
  it is not loop code), each with its own `_with_prefix` sequencing and `Seq`
  and `If` handling;
- function bodies: `execute_c_function_body_paths` and
  `execute_c_function_body_verification_paths` (`src/kernel/functions.rs`),
  two nearly identical goto loops;
- function application: `execute_c_function_paths_with_contract_resources`
  and `execute_c_function_verification_paths` (`src/kernel/functions.rs`),
  about 250 lines each.

Differences between the copies that the judgments do not account for:

- An abnormal first outcome of `Seq` (break, continue, jump, return, throw,
  undefined behavior, runtime error) is rebuilt with
  `CStatementExecutionPath::new` in the ordinary driver. That drops the
  path's `loan_evidence`. The verification driver keeps it.
- Only the ordinary `Seq` continues a `pending_thread_create` across the
  sequence. Only the verification function path installs the recursion
  anchor (`c_function_recursion_anchor`).

Whether any of these is observable from a Click proof is not yet established.
Reproduce each before treating it as a bug, and file in `bugs/` any that
changes a verdict.

The invariant: one implementation steps a statement. The judgment (concrete
or verification) and the `CExecutionSemantics` mode are parameters of that
implementation, not reasons to copy it. Every difference between the two
judgments is a named, documented branch in that one implementation.

## Intended regression

Add kernel regressions that run the same statements under both judgments
where both apply. Cover a `Seq` whose first statement breaks, returns, throws
or reaches undefined behavior while it holds loan evidence, and a sequence
across a thread-create. Assert that the concrete path set is contained in the
verification path set, with matching loan evidence. Keep the existing
`execution_tests`, `heap_tests` and `thread_transition_tests` passing
unchanged.

## Acceptance criteria

- One statement driver and one function-body driver serve both judgments. The
  judgment-specific behavior (`VerificationDiverges`, rule application, the
  recursion anchor) is an explicit, documented parameterized branch.
- `execute_c_statement_verification_paths` and its `_with_prefix` twin are
  removed, or reduced to thin wrappers that select the judgment.
- Each observed drift above is either shown to be required by the judgments
  (and documented in `kernel.md`) or removed, with a regression.
- `docs/internals/kernel.md` describes the single driver.
- The gate and the nightly corpus show no verdict changes. Any change that
  does appear is filed and explained.
</content>
</invoke>
