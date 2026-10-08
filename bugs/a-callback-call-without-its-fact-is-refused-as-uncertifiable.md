# A callback call whose contract fact is gone is refused as "cannot yet certify"

## Violated invariant

A refusal names what the proof lacks. A call through a function pointer with
no contract fact for that pointer lacks the fact, and the diagnostic must say
so.

## Reproduction

```sh
click verify mdtests/rb_augment_callbacks_helper_rejects_changed_cell.md
click verify mdtests/rb_augment_callbacks_helper_consumes_suite.md
```

Both report

```
the proof script is valid, but the verifier cannot yet certify it for these 2
contract claims: `erase_changed.owns: owns parent->left`,
`erase_changed.owns: owns parent->right`. It reached tactic 0 (resource
scope), which is not implemented in this execution context.
```

In the first, a helper replaced the `copy` cell of an owned callback suite,
so the suite's old `Copy` fact does not describe the pointer the next call
applies. In the second, the suite was consumed, so no callback fact remains.
Each proof is wrong for that reason, and neither message mentions it.

## Cause

Until reads went through an owned resource (`issues/design-review.md`, B3),
both proofs stopped earlier: the call could not read the callback pointer
out of the folded suite, and the refusal was "missing resource fact". The
read is now authorized, so the checked execution reaches the call itself,
finds no contract fact for the pointer, and declines without a diagnostic.
The fallback route then reports that it does not implement the proof's
`open` scope.

The earlier message was not the intended one either: it named a missing
view, not the stale or absent callback fact.

## Intended regression

The two mdtests with an `expect` line that names the missing callback
contract, for example "no contract fact for the function pointer
`augment->copy`".

## Acceptance

- Both mdtests are refused by a message naming the callback pointer and the
  contract fact it lacks.
- Neither reaches the "cannot yet certify" fallback.
