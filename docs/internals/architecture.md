# Architecture

Click is divided into one specification language, Surface Click, a family of
supported target languages, a kernel semantic core, and command-line
orchestration. Both the specification language and each target language have
frontend stages such as parsing, validation, and lowering; *frontend* names a stage, not either
language's role.

The shared kernel loop node is `ProgramStatement::Loop`: it represents structured
loops and checked natural cycles. Source ASTs retain their language-specific
`While` forms; `program_while` and `program_do_while` construct the corresponding
pre-test and post-test forms of the shared node.

A loop owns its optional update and one mandatory `LoopTestRegion`. Every
test has a placement before or after the body and a shared code region. A
pure test contains just `LoopTest`, which owns its condition and temporary
cleanup. A prepared test prefixes that same decision with its calls or other
preparation. The loop has no separate condition or `do_while` flag.
A borrowed execution view reads a preparation-free decision directly; prepared
tests enter their code region before the decision is available. This keeps
existing proof-step numbering without storing a second test on the loop.
`program_loop_pass` assembles the shared phase references for checked source
execution; `program_loop_continuation` selects the update and post-test owed
by a continuing edge. Normal body completion and `continue` leave the body
scopes before entering that continuation. A `break` or function exit skips it.
The evaluator and execution frontier follow the same regions; invariant and ranking
obligations close only after the continuation reaches the backedge. A false
post-test instead supplies a loop exit with its own state and facts.

Source layout indexes each update/test once and records the continuation entry
directly. Persistent lexical-scope exit lists distinguish leaving the body on
`continue` from leaving the function on `return`, including transfers emitted
by an atomically executed switch. For-initializer storage remains live across
updates and tests and ends when the loop exits.

## Repository map

| Path | Responsibility |
| --- | --- |
| `src/languages.rs` | Select target languages and package prepared program execution. |
| `src/languages/interface.rs` | Shared imported declarations, interface types, callback metadata and record layouts. |
| `src/languages/c.rs`, `src/languages/c/` | Parse supported C and implement C compatibility and lowering. |
| `src/languages/cpp/`, `src/languages/rust/` | Import native compiler artifacts and lower them to shared program execution. |
| `src/surface.rs` | Define Surface Click forms and connect its checking, lowering, proof, and presentation modules. |
| `src/surface/parser.rs` | Tokenize and parse Surface Click; share exact token spans with source tools. |
| `src/surface/names.rs` | Resolve library imports and theorem shadowing; share those bindings with source printing. |
| `src/surface/printing.rs` | Print Surface proof text and propositions with an explicit source or refusal mode. |
| `src/surface/validation/` | Resolve declarations and enforce source-level type and form rules. |
| `src/surface/lowering/` | Translate checked surface contracts, propositions, resources, and source locations. |
| `src/surface/checking/` | Evaluate contract forms and connect them to kernel structures. |
| `src/surface/proof/` | Interpret tactics, orchestrate checked proof operations, run smart search, and synthesize surface expansions. |
| `src/source.rs` | Share source-file positions between Surface Click and target-language frontends. |
| `src/kernel/` | Define primitive terms, states, rules, symbolic execution, assumptions, memory reasoning, and the persistent checked proof object. |
| `src/cli.rs` | Shared CLI parsing, target selection, durations, and user-facing command metadata. |
| `src/bin/` | Thin entry points and command-specific reporting for verify, profile, expand, audit, and import, plus the `click` dispatcher's version manager (`install`, `use`) in `src/bin/click/`. |
| `src/instrumentation.rs` | Work attribution, deadlines, budgets, and profiler events. |
| `src/persistent.rs` | Persistent structures used where proof states share prior versions. |
| `library/` | Click library modules loaded with user source. |
| `mdtests/`, `examples/` | End-to-end proof fixtures. |

## Data flow

Surface Click parsing and target-language imports retain source locations. Validation builds a `ProgramVerificationSession`, which owns checked declarations and function blocks.
Lowering records the relationship between surface propositions and kernel
propositions so diagnostics and expansion can return to source language.
Those records are presentation hints, not evidence that a fact is available.
Loop-head lowering returns one selected proposition per declared invariant,
including duplicates, separately from the new-fact delta. A preservation
proof records generated iteration-entry spellings against those selected
propositions in its local scope; an unqualified source spelling continues to
lower against the current execution state. Certificate generation checks a candidate
spelling at its output location and validates the selected kernel premise,
never whichever available fact happens to share that spelling.

The kernel's persistent `ProofObject` owns typed obligations, facts, symbolic
program execution, resources, focus, and checked successor authority. A
Surface-layer `Proof` pairs that opaque handle with checking context and
Surface provenance. Explicit tactics request named simple or structural
operations. Smart planners try the same operations transactionally on
persistent `Proof` descendants; they can't construct semantic successors
directly. Kernel APIs expose the primitive logical, execution, memory, and
resource operations needed for that checking.

`ProofDriver` interprets source and generated proof trees over the persistent
`Proof`. It chooses explicit operations or `ProofSearch`, including implicit
solving for obligations without written proof blocks. Omitted obligation proofs
invoke the same solver as explicit `solve()`; only scheduling and source
attribution differ. `Proof::prepare_step`
produces the existing candidate and obligations; the driver proves them at the
original frontier and publishes the retained result through `finish_prepared_step`.
Completion never reruns the operation. A preparation refusal is final; code that
needs a premise must emit an obligation while retaining its conditional result.
Assertion failure obligations retain their producer tag, so preparation can
select the sole successful assertion arm without reconstructing its Boolean
meaning. Definedness preparation retains the sole defined arm and emits its
path guard. Neither candidate supplies evidence for its own prerequisites.
This is one
engine switching between operations and search as it interprets the proof. Remaining operation calls
back into the driver are frozen in the
[dependency inventory](https://github.com/clicklang/click/blob/master/build_support/proof_search_edges.tsv); the split
does not yet establish search-free explicit operations. A proof shape no driver
accepts is a terminal error, never a reason to run a second engine.
`ExecutionProofState` is the typed execution state inside a `Proof`: the
frontier, path state, and surface record it owns are the execution model, and
the only cursor it carries is where a source tactic's expansion is being
captured.

`ProofCertificate` is the current structured form for a surface-expressible
explicit proof. In the intended architecture it is serialization: expansion
extracts attributed operations from checked `Proof` provenance only when proof
text or an inspection result is requested. Scalar return expressions can
produce distinct outcomes without a written C branch; certificate synthesis
separates their different endings with a guard each outcome decides. Guards
from conditional result claims retain their written field places when used as
normalization premises.

### Contracts and callbacks

One body-independent contract interface carries a function's typed
parameters and result, proof binders, pure requirements and guarantees,
normalized resource clauses with their access, transfer role, and state,
composite definitions, and predicate unfoldings. Verified functions, external
assumptions, named callback contracts, and execution theorems all apply
through it; their evidence stays distinct (a callback fact is tied to an exact
pointer value, an external assumption is never a verified body).

Each application prepares one resource transition: borrowed and consumed
inputs, the caller residual, the callee's context, the memory-effect
projection, and the post outputs. It has two purposes. A call site lends, so
the views it passes become loans and recovery returns them. A function
boundary, the verified-body executors, the contract entry-state builder, and
the outcome-through-contract applier, consumes the declared requirements
definitionally; its input-view loan roots come from the proof's entry
construction, so nothing is lent twice. The two agree on what the callee
receives. The callee's pure preconditions and its returned borrows are read
against the transferred clause set opened through its definitions, the way the
callee's own entry reads it.

The memory-effect projection of that transition is the only write footprint:
modular call havoc, refinement containment, certification's effect claims,
storage-write checks, and every loop frame (inherited at function entry or
declared at loop entry) derive from it. A frame check across a call or loop
havoc opens an owned composite one level, the boundary a composite lend and
`project` use, and never reads inside a folded body.

Instance binders reach one kernel map whether a proof writes a call map or a
named contract's proof arguments; an execution theorem's `as` map only renames
spellings before binding through one of those. The loan ledger, its laws, and
the call boundary's lending and recovery are in
[stable views](stable-views.md).

## Selected control-flow and C++ cleanup model

The launch control-flow slice has one checked execution-frontier model for
forward C edges and C++ cleanup edges. A frontier carries its path state and
obligations to the next source operation; a transfer does not execute skipped
statements. C forward `goto` keeps its target and source attribution, while the
C++ importer supplies checked destructor operations on normal returns and
exceptional unwinding edges. The language frontends decide which edges are
legal; the kernel does not infer cleanup or loan recovery from lexical scope
alone.

The `scalar_int32` C++ exception profile is deliberately closed: C++20 on the pinned
Clang/LLVM 19.1.7 `x86_64-unknown-linux-gnu` profile, exceptions enabled,
RTTI disabled, one `int32` exceptional payload, a matching `catch (int)`, and
non-throwing constructors and destructors. `throws int32` is part of the
checked Click signature. Normal `ensures` and `exceptional ensures` are
separate claim families; a missing exceptional declaration is non-throwing,
not an unconstrained promise. The locked exporter artifact records the
compiler profile and semantic input, so an exporter change cannot silently
broaden a normal-only import.

The separate `ios_failure` profile propagates the exact opaque
`std::ios_base::failure` class, without handlers or user cleanup. Its pinned
standard-library constructor lowers to a fresh abstract value from a catalog
factory; the runtime owns storage and destruction, and allocation failure is
assumed to terminate. Direct exceptional interfaces can borrow raw memory:
normal and throwing call successors share footprint-bounded havoc, but receive
only their own postcondition family. Both successors use the existing joint
resource-return and loan-recovery operations. Outcome claim cells keep borrowed
resource ensures open on throws instead of marking every normal-family cell
vacuous. Named callback refinement remains pure `int32`.

The `typed` profile also admits ordinary trivial aggregate prvalues and
empty exception tags. It evaluates explicit scalar field initializers in
source order through ordinary value steps, then `ThrowOpaque` allocates a
fresh value of the imported nominal type and returns the current state.
Class types use an elaborated `struct Name` identity distinct from generic
type parameters. Construction has no trusted user-constructor contract;
nontrivial copying, destruction and class handlers remain refused.

C++ record-reference locals reuse the parameter carrier (`&name`) and retain
the record layout in the imported function's local struct-pointer metadata.
Surface therefore resolves `name.field` as a record place, without treating the
alias as a new object or granting memory authority. Binding through a record
pointer uses checked address formation on a byte-array lvalue of the complete
record size, followed by the adapter's existing record-pointer representation.
The address rule validates storage without reading the array or its fields.
Automatic destructor cleanup emits the existing storage-lifetime-end operation
after the destructor returns, so an alias cannot keep a scoped record alive.

C++ `declared_noexcept` is retained in the shared imported declaration as
`requires_nonthrowing_contract`, including dispatch aliases. Signature
checking refuses `throws` on that interface; the existing nonthrowing body
judgment proves that all reachable exits are normal. A guarded call may use
its callee's exceptional guarantees to refute the exceptional path. Modular
eligibility depends on the interface, while checked body safety establishes
that internal throws are caught or excluded by its preconditions. No
termination behavior is assumed from a `noexcept` spelling. Opaque exception
profiles still refuse automatic destruction in potentially throwing functions;
the already-built lifetime plan detects that restriction in nested scopes too.
A caught scalar throw retains the after-try continuation in both the Surface
frontier and checked statement-evidence cursor, so a normally completing
handler resumes the enclosing function.

C++ void fallthrough lowers to an explicit kernel return, as C void fallthrough
does. This gives a final maybe-throwing call a normal continuation for `outcomes`
without adding a statement to the original source.

The C++ exporter uses Clang's typed AST and checked source CFG to identify the
throw, handler, payload, and constructed objects. It emits destructor calls as
ordinary checked kernel steps, in reverse construction order, and retains the
constructed prefix when a later declaration follows a potentially throwing
call. Function-scope destructor chains also run before an escaping call or
explicit throw crosses the function boundary, including when a potentially
throwing call initializes a local. ABI landing pads and runtime exception
behavior are trust-boundary inputs, not proof evidence. The supported slice
permits at most two destructible objects in the selected cleanup scope;
throwing constructors or destructors, rethrow and inherited handlers,
`setjmp`/`longjmp`, and general backward or irreducible edges remain outside
it.

The [resource tracker](resource-tracker.md) is the single kernel authority for
whether a mutable resource is the same at two proof points. Cleanup proofs use
that answer to frame destructor stores and to distinguish a real mutation from
an unshown fact; it does not grant ownership or recover a resource on its own.
The semantic regressions are `mdtests/cpp_two_guard_unwind.md`,
`mdtests/cpp_guard_unwind_before_second.md`, and
`scalar_int32_profile_emits_function_scope_cleanup_edges_for_escaping_throws`
in `tests/cpp_import.rs`. The deterministic
scaling regression
`exceptional_cleanup_edges_scale_near_linearly_with_unrelated_context` in
`src/scaling_tests/surface/tests/scaling_tests.rs` covers cleanup-edge counts 2, 4, 8, and
16 while unrelated functions and facts grow; it checks both total work and
the named call/edge operation rather than wall time.

## Trust and boundaries

The kernel semantics and the code that translates accepted source claims into
kernel obligations are in the trusted computing base. Smart planning isn't:
it can advance proof state only through checked operations. CLI rendering and
profiling don't decide validity. Expansion is accepted only after the complete
rendered source verifies through the ordinary entry point.

In particular, function-entry lowering represents the declared inputs with
symbolic values and constructs the entry resources. Kernel certification checks
the execution evidence against that supplied entry; it does not redo the source
translation. Thus "Surface" contains both trusted obligation construction and
untrusted smart planning. See [Source obligations and checked
evidence](kernel.md#source-obligations-and-checked-evidence) for the contract
pipeline and its caller responsibilities.

The ordinary `Proof` transition boundary and rewritten-source verification
are the durable invariants; no separate certificate validation sits in front of
that check.

OS process wrappers aren't part of the proof architecture. CLI commands and
fixture gates call the shared bounded verification engine directly. Deadlines
contain hangs; deterministic work budgets define normal proof-search bounds.

## Extension paths

When adding a public surface, change its authoritative implementation and its
reference inventory in the same slice:

- a Surface Click form normally touches the parser, syntax type, validation,
  lowering, printing, tests, and language reference;
- a tactic touches the surface enum/parser, classification, its checked `Proof`
  operation or smart planning, printing/expansion, tests, and tactic reference;
- a kernel rule needs a focused kernel regression and an explicit account of
  why the rule is sound;
- a CLI option belongs in shared metadata and command tests before its
  synchronized reference entry;
- a Click library declaration belongs in a `library/` module, an mdtest,
  and the source-checked library reference.

See [Feature playbook](feature-playbook.md) for the review sequence and
[Testing](testing.md) for the complete gate.
