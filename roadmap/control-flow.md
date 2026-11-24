# P2: Extend bounded control flow

Priority: P2.

Soundness: incomplete. Unsupported switch, cleanup and unwind shapes are
refused. On 2026-10-12, `return 0 && bump();` was checked with the release
binary: the unselected call contributed no effect, and a false claim that it
ran was refused.

The selected P1 control-flow milestone is complete: structured C loops and
loop exits, constant-expression-label `switch`, checked forward `goto` cleanup,
and the bounded C++ cleanup/unwind profile all have checked execution and
regression coverage, including a conditionally constructed guard around a call
that can return or throw into a returning handler. This issue records
independently motivated extensions that can improve ordinary control-flow
coverage without taking on general backward or irreducible `goto`.

This is deliberately not the home for verifier-wide control-flow soundness
audits; file those findings as their own P1 issues or `bugs/` entries when
they are found. General backward, multi-entry, and irreducible jump graphs
remain deferred in [`goto.md`](goto.md).

## Remaining short-circuit gap

Calls in short-circuit operands are delivered:
`mdtests/calls_in_short_circuit_operands.md` covers selected and unselected
calls under `&&` and `||`, an unselected callee whose precondition is
impossible, a selected callee that writes a global, and a call in a loop
condition. `mdtests/qualified_static_wide_values.md` is not quarantined.

No regression yet nests `&&` and `||` with calls, as in
`a() && (b() || c())`, where an inner operand is selected or skipped by both
levels. Add one, with selected and unselected writes and an unselected callee
whose precondition is impossible, keeping the source unchanged rather than
rewriting it into `if` or adding proof-only locals.

## Delivered `switch` shape

Integer constant-expression labels in one compound body, fallthrough, and
nested switches are delivered (`mdtests/c_switch.md`,
`mdtests/c_unsigned_switch*.md`,
`mdtests/automatic_scope_exit_nested_switch*.md`): an inner `break` exits the
innermost switch, fallthrough keeps an inner local alive, a `continue` reaches the innermost
enclosing loop and retires that local, a scalar `return` reads it before
cleanup, and a case-local constructed on one dispatch path is retired when
sibling paths join. Jumping into or across a switch belongs to `goto.md`.

## Broader cleanup and unwind edges

The selected C++ profile checks a bounded scalar exception, matching handler,
and up to two non-throwing destructible guards. It also accepts one guard
constructed conditionally inside a `try` when the selected `int32` handler
returns: the skipped branch constructs no guard, the normal call outcome runs
the guard's cleanup and reaches the enclosing continuation, and the caught
outcome runs cleanup and returns. The [C++ import regression](../tests/cpp_import.rs)
verifies the unchanged source, expands and reverifies its proof, and audits the
expanded result. A kernel regression checks the distinct terminal paths; a
proof-object regression checks the enclosing continuation and per-path call
edge selection. This does not claim arbitrary nested `try`/`catch`, an outer
cleanup lifetime, or multiple conditional guards.

Broader support remains a larger architectural slice. Candidate shapes include
more constructed objects, richer handler selection, and additional normal or
exceptional scope exits.

The hard requirements are to preserve the constructed-object stack, emit
destruction in the language-defined order, keep returned and thrown states
separate, and reject unsupported constructor/destructor or handler behavior.
The importer must record the selected compiler/profile assumptions; ABI
landing pads and runtime behavior are not proof evidence. General backward or
irreducible edges, rethrow, `setjmp`/`longjmp`, and throwing destructors remain
out of scope here.

For each further edge shape, start with a small source example that identifies
the new behavior and a hostile negative. A regression must cover
both the normal and exceptional outcomes, expansion/reverification, and the
relevant deterministic scaling boundary.

## Shared invariant

Every accepted transfer or conditionally evaluated operation carries the
complete state and obligations at that point. Skipped statements and
unselected operands contribute no effects; cleanup runs exactly for objects
whose construction completed; and every accepted path remains visible in the
checked certificate.

## Suggested order

1. The nested short-circuit regression above.
2. A narrowly motivated cleanup/unwind extension, such as one around nested
   switches.

Revisit general `goto` only after its edge, scope, and termination model is
designed independently in [`goto.md`](goto.md).
