# A verified two-to-one quantity contract cannot be applied at a call

## Violated invariant

A function contract whose own proof verifies can be applied at a call site
whose caller supplies the contract's inputs. Under authority semantics, a
helper that consumes two units of a tracked family and produces one verifies
as a standalone proof, but every call to it is refused:

```
function contract could not be applied
helper contract needs conserved owns resources, a checked consumes/produces effect, or a supported unit exchange
```

The explicit quantity shape `consumes 2 of R(p); produces R(p);` is accepted at
the definition and proved in the body. The call boundary admits only conserved
`owns`, single-unit consumption/production effects, and checked unit
exchanges, so it has no rule for the net one-unit change this contract states.

## Reproduction

Start from `mdtests/shared_heap_two_parent_caller.md` on current `master`, which
verifies. Replace only the `parent_detach` contract's resource clauses:

```text
    consumes child_control(p->kid);
    produces child_control(old(p->kid));
    owns child_ref(p->kid);
    consumes child_ref(p->kid);
```

with the contract this C was originally written against:

```text
    consumes child_control(p->kid);
    produces child_control(old(p->kid));
    consumes 2 of child_ref(p->kid);
    produces child_ref(old(p->kid));
```

The C, the proof body, and the caller are unchanged. `click verify` on a
location inside `parent_detach` reports `1 selected proof verified`. Verifying
the whole file fails at `caller` on `step(parent_detach(first), ...)` with the
error above. The caller holds three `child_ref(kid)` units at that call (the
creator's reference plus one from each `parent_attach`), so the contract's
inputs are available.

A variant that also returns control only under
`if old(count(child_ref(p->kid))) > 1 { ... }` fails at the same call for the
same reason. Keeping the guard but restoring the `owns`/`consumes` member shape
verifies, so the guard is not the cause.

## Intended regression

Add a focused authority-mode fixture with an ordinary counter/authority control
and an empty member family. A helper borrows the control, consumes two members,
produces one, and decrements the C counter by one. Its caller births three
members, calls the helper, and proves the count and its remaining custody of
two members.

Negative companions must reject: a caller holding only one member; a helper
body that produces two members while declaring one; and reuse of a consumed
member after the call.

## Acceptance criteria

- The reduced fixture and the unchanged-C `shared_heap_two_parent_caller.md`
  variant above verify under authority semantics, with the caller observing the
  net population change of minus one.
- The call boundary checks the multi-unit exchange against the helper's
  independently verified effect and the caller's actual custody. It does not
  derive custody from the global count.
- The negative companions fail with diagnostics that name the missing member or
  the false count.
- Kernel and certificate checks admit the exchange in work proportional to the
  stated quantities and the affected population, with a multi-size scaling
  regression beside unrelated populations.
