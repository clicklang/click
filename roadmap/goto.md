# P2: General backward and irreducible `goto`

Priority: P2.

Soundness: incomplete. Jump shapes outside the delivered forward and
natural-cycle subset are refused by the parser.

This is intentionally deferred P2 work. The selected control-flow milestone
does not depend on it, and the bounded extensions in
[`control-flow.md`](control-flow.md) must not broaden accepted jump shapes as
a side effect. Start this issue only when one edge family has a bounded,
source-attributed execution and termination rule.

Found during the 2026-09-03 control-flow follow-up after commit 184b4ef2.

The P1 forward-cleanup prerequisite for the selected control-flow demo landed
in commits `9e247956`,
`2e3bdcb9`, and the cleanup-chain regression linked below. Click now has
checked forward edges from function bodies and `if` arms to later
function-scope labels, exact target resumption, path joins, and chained
ordinary C cleanup. This issue now tracks only the deferred general jump
shapes.

Click accepts the documented forward subset, including forward jumps out of
a loop or switch to a later label, and one narrow reducible natural-cycle
subset: a direct function-body entry label with backward edges from its
re-entered region, possibly nested in an `if`, where the existing `loop`
proof supplies the invariant and termination evidence, and forward exits
sharing one later label. The accepted shapes are listed under `goto` in
[the C language reference](../docs/reference/language/c.md). General backward
edges, loops or switches after a label, distinct forward exit targets from a
cycle, labels nested below the function body, and edges across unsupported
declaration scopes remain rejected. Treating those shapes as
`break`, a hidden flag, or a source rewrite would lose the C control-flow
semantics that Click is meant to verify.

## Cross-language edge design

Design the execution frontier and checked edges with the future language
frontends in mind. The delivered [basic C++ slice](../examples/basic-cpp/README.md) implements
implicit cleanup on ordinary scope exits and returns without general C goto.
The [one-guard exception regression](../mdtests/cpp_one_guard_unwind.md) now
checks cleanup on one exceptional call edge as well; the completed bounded
two-guard unwinding case is recorded in the
[control-flow architecture note](../docs/internals/architecture.md#selected-control-flow-and-c-cleanup-model).

A target label alone is not enough for every language. An edge may need
checked scope-exit operations, object-lifetime changes, and a distinction
between normal transfer and unwinding. C++ can require destructors on scope
exit and restrict jumps across initialization. Rust MIR has block edges and
conditional drops, even though Rust has no source `goto`. Borrow expiration
must remain distinct from lexical scope exit and object destruction.

Keep the edge mechanism shared and its legality/cleanup rules language-specific.
In particular, do not apply C++ initialization restrictions to every C jump,
or assume that skipped lexical statements account for all implicit effects.
Capturing a return value must precede the cleanups required before returning
to the caller. Carry source attribution for those implicit operations into
the certificate and diagnostics.

Before fixing the representation, check it against a forward C cleanup jump,
a C++ RAII early return, and a Rust conditional-drop edge. These are design
checks; this issue does not require implementing the other language frontends
or exception handling. The control-flow demo owns the selected cross-call C++
exception probe. Reuse the basic C++ cleanup-edge work without introducing a
dependency cycle between the remaining issues.

## Violated invariant

Every accepted C control-flow edge must be represented in the kernel semantics
and in the checked proof certificate. A jump must carry the complete C state
at the jump, apply any required checked scope-exit effects, and resume exactly
at its target. Ordinary statements skipped by the jump execute on neither
the jump path nor its proof trace.

## Delivered boundary

The forward regressions are the `mdtests/forward_goto_*.md` files and
`mdtests/goto_out_may_skip_loops_that_precede_its_label.md`: checked edges,
skipped statements and conditionals, path joins, label chains, allocation
cleanup, jumps out of `while`, `for` (retiring the initializer's locals),
switches and summarized loops, expansion, and hostile missing cleanup or
wrong joins. The natural-cycle regressions are the `mdtests/natural_goto_*.md`
and `mdtests/a_natural_goto_cycle_*.md` files: single and conditional
backedges, multiple backedges, exit labels, forward exits with differing
states, and returns from a cycle. `mdtests/goto_refuses_a_loop_after_a_label.md`
and parser tests retain the unsupported-shape diagnostics.

## Intended regression

The delivered natural-cycle slice covers a small backward edge whose cycle has
an explicit invariant and deterministic termination measure. The proof resumes
at the exact label with the current path state, rejects an omitted or
non-decreasing measure, and expands to a checkable certificate. Future work may
begin with one independently motivated multi-entry or irreducible shape only
if its edge invariants, source attribution, and termination rule are bounded.
Do not infer general support from the simple cycle or from the multiple-exit
and multiple-backedge extensions.

## Acceptance criteria

- Backward edges use explicit checked invariants and termination evidence;
  an execution or tactic budget is never accepted as a termination proof.
- The parser assigns each accepted edge a source-attributed target and rejects
  entry into scopes whose declarations or language-specific lifetime rules
  make the edge illegal.
- The kernel edge carries its exact state, obligations, and target through a
  checked certificate without hidden flags or source rewrites.
- Multiple entries or irreducible regions, if added, state and check their
  join interface per incoming edge without scanning or cloning unrelated
  function state.
- The edge/scope representation has an explicit account of the C++ cleanup
  and Rust drop design checks above, with language-specific legality and
  reserved normal/unwind distinctions. It does not require a second proof
  engine or treat every scope exit as automatic borrow recovery.
- The general-jump regressions and `scripts/check.sh` pass.
