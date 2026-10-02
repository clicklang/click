# Contract setup and callback refusals don't name a source location

## Violated invariant

Every refusal about a C program should say where in the source it applies.
Refusals of a single step print `C statement at file:line` plus the source
text, and so do refusals about a whole execution path: a leak or a mutex
still initialized at a `return`, and a scope a `break` or `continue` leaves.
Two kinds of failing output still have no location:

- contract setup failures, such as
  `` `release.contract` setup failed: could not evaluate the contract entry resources ``;
- callback theorems with no C body.

Neither has a C statement to name. A setup failure is about the function's
contract at entry, so the location to print is the C function's declaration
or the contract clause the message already counts (`resource clause 1 of 2`).

## Intended regression

An mdtest for a contract setup failure that pins the location line and the
source text it names, and one for a refused callback theorem.

## Acceptance criteria

- A setup failure prints where the function or the failing clause is written.
- A refused callback theorem prints where its declaration is written.
- The location is diagnostics only: it must not affect identity, interning,
  caching or work.
