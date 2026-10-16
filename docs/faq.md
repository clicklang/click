# Frequently asked questions

This page answers common questions about using Click and contributing to it.
Each answer links to the reference that defines the current behavior.

## What is Click, and do I have to change my program?

Click verifies properties of existing C, C++, and Rust programs. Contracts and
proofs live in `.click` sidecars beside the implementation. Keep correct source
as written and put proof work in the sidecar. Unsupported source features are
coverage boundaries to report; they do not justify rewriting the program just
to get a proof through. Start with [your first proof](concepts/first-proof.md)
and [what Click proves](concepts/what-click-proves.md).

## What does a passing proof guarantee?

For the selected claim, every modeled input satisfying its requirements leads
to executions that avoid the checked runtime errors, terminate, and satisfy its
postconditions. A `diverges` contract permits nontermination. The guarantee
depends on the recorded target and assumptions; it does not cover host limits
such as stack or memory exhaustion. See [what Click proves](concepts/what-click-proves.md)
and the [runtime-error coverage](reference/coverage.md#runtime-errors-checked).

## What must I trust, and why is the kernel large?

The trusted base includes Click's kernel, claim lowering, target-language
frontends and models, and declared external contracts. Click deliberately puts
domain-specific machinery in the kernel to prioritize verification performance
and useful systems-code reasoning. Smart search advances proofs through kernel
operations; it is outside that trust boundary. There is no independent proof
checker, and expansion uses the same verifier. [What Click trusts](concepts/trust.md)
states the boundary and its tradeoffs.

## Which languages and platforms are supported?

C is the primary target language; C++ and Rust support is experimental. Each
frontend admits a documented subset. The modeled target is x86-64 Linux with
the documented ABI; a proof does not establish portability to other targets.
The packaged Rust extraction frontend also requires a Linux x86-64 GNU host.
Use the [coverage matrix](reference/coverage.md) to check individual features
and distinguish a verification target from the host running Click.

## How do I install Click, and when do I need `--rust`?

From a checkout, use `cargo install --path . --bin click`. The
[README](https://github.com/clicklang/click#install-click) records release
availability and installer commands. A normal installation supplies the Click
executable; `click install VERSION --rust` adds the pinned Rust frontend and
compiler runtime for release `VERSION`. Plain C verification needs no compiler.
Rust extraction needs its frontend, while verification of an existing valid
Rust lock does not. C++ extraction uses a separately built pinned exporter. See
[installation and version selection](reference/cli/versions.md),
[Rust setup](reference/rust.md#installed-rust-frontend), and
[compiler imports](reference/cli/import.md).

## When do I run `click import lock`?

Run it to prepare or refresh compiler-backed inputs. It records the source
inputs, configuration, toolchain identity, and extracted artifact in the
project lock. Ordinary verification reads the prepared inputs offline and
refuses a stale lock; it does not refresh the lock automatically. Direct C
parsing needs no compiler import. See [project units](reference/cli/import.md#project-units)
and [locked Rust imports](reference/rust.md#reproduce-the-example).

## How do I use Click with my project's build settings?

Put contracts in sidecars and describe compiler-backed sources in
`click.project.json`. The project configuration identifies units, source roots,
and supported build settings; Click does not discover the build's compiler
flags for you. [Verify a function in your own project](concepts/own-project.md)
walks through include paths, defines, locks, libc calls, and calls across files.
The [project-unit reference](reference/cli/import.md#project-units) defines the
configuration shared by C, C++, and Rust units.

## Does verifying one function also verify all its callees?

Verification is modular. A caller uses a callee's contract; checking that
caller alone does not prove the callee's implementation. Imports also make
declarations available without selecting all their proofs. External contracts
are assumptions, and verification reports dependencies on external interfaces.
Check the intended set of proof units and read the reported assumptions. See
[verification selection](reference/cli/verify.md#target-selection) and
[your assumptions](concepts/trust.md#your-assumptions).

## Does the Rust borrow checker supply memory permissions?

Rust's compiler establishes source type and borrow legality. Click checks the
functional contract and the extracted execution's memory obligations.
References still need explicit `owns` or `views` clauses for the memory they
access; a reference does not supply allocation or deallocation authority. The
[Rust borrow and proof boundary](reference/rust.md#borrow-and-proof-boundary)
describes the supported local borrow protocol and its limits.

## Does a failed proof mean the program is wrong?

A failure can come from a false claim, missing prerequisites, an incomplete
proof, an unsupported construct, or a verifier defect. Smart search can miss a
valid proof within its work budget. Inspect the failed obligation, try relevant
explicit steps, and use `click verify --trace-proof FUNCTION PATH`, replacing
`FUNCTION` with the proof name and `PATH` with its sidecar. Follow
[proof-failure triage](concepts/proof-failure-triage.md) before changing the
program or blaming the verifier.

## When should I use verify, profile, expand, and audit?

Use `verify` to establish correctness, `profile` to locate verifier work, and
`expand` to turn successful smart tactics into explicit proof source. Verify
the rewritten source. Use `audit` to check expansion, fresh and retained
verification, and the documented performance policy across selected proofs.
These tools share the verifier's trust boundary. See
[performance tools](concepts/performance-tools.md) and the
[CLI reference](reference/cli/index.md).

## Has Click verified real third-party code?

Yes, for specific functions and contracts in unchanged upstream source.
Those results retain explicit input, seed, target, and dependency boundaries;
they do not imply that the entire containing library is verified. The
[upstream coverage summary](reference/coverage.md#unchanged-upstream-source)
names the evidence, and the [integration projects](https://github.com/clicklang/click/tree/master/integrations)
record their pinned source and reproducible claims.

## Where do I find current limitations and planned work?

The [coverage matrix](reference/coverage.md) and
[limitations reference](reference/language/limitations.md) describe current
behavior. Reproduced defects live in
[`bugs/`](https://github.com/clicklang/click/tree/master/bugs); planned work
lives in [`issues/`](https://github.com/clicklang/click/tree/master/issues).
Check linked pull requests for fixes awaiting merge. Historical experiments
and design proposals describe their stated revisions, not additional supported
behavior. See [contributing](internals/contributing.md) for filing rules.

## Which tests should I run for a contribution?

Run focused checks for the behavior being changed. `scripts/check.sh` is the
full gate run by CI; `cargo test` alone does not establish that verdict.
Prose-only changes can use `scripts/check.sh --docs-only`. Run relevant nightly
tests by name rather than the whole nightly suite. [Testing Click](internals/testing.md)
documents fixture filters, expansion checks, and test budgets; the
[contribution workflow](internals/contributing.md) covers pull requests and
the merge queue.
