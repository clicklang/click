# Use the short proof forms in the existing proofs

Priority: P2.

## Violated invariant

The examples, standard library and mdtests are what a reader learns Click
from, so they should be written the way the language now reads best. Three
short forms landed after most of them were written, and the corpus still
spells the long forms:

- `by T(args);` for a one-step proof, where the corpus writes
  `by { T(args); }` (#332). `by simp;` already existed for `by { simp(); }`.
- `have P;`, which is `have P by simp;` (#313).
- `instantiate(F, value);` without a `using` list, which looks each
  instantiated guard up as an exact fact (#307), where the corpus retypes the
  guards in a `using` list or writes an empty one for an unguarded fact.

Counted on 2026-10-07 in mdtests, examples, stdlib and integrations: 700
`by { simp(); }`, 147 `by { assumption(); }` and 70 `by { normalize(); }`.
There are about 200 `instantiate` calls with a `using` list. How many of those
lists are exactly the guards has not been counted; trying the bare form on
each call and keeping the ones that still verify gives the number.

## Scope

A mechanical rewrite with no change to what any proof proves:

- `by { simp(); }` to `by simp;`, and on a `have` to no proof at all where
  that reads better;
- `by { T(args); }` to `by T(args);` for a single tactic written as a call;
- `instantiate(F, v) using { ... }` to `instantiate(F, v);` where the proof
  still verifies, which is exactly when every listed premise is an
  instantiated guard that is already a fact.

Leave a multi-step block, a block form such as `both { ... } and { ... }`, and
any `instantiate` whose list derives a guard from other facts. Do not touch
the hash-pinned frozen sidecars under `design/charon-trial` without updating
`parity.json`, and do not change an mdtest whose point is the long spelling
(for example `empty_using_list_is_accepted.md`,
`by_takes_one_tactic_without_braces.md`).

## Intended regression

None new: the rewritten proofs are the regression. The forms themselves are
covered by `by_takes_one_tactic_without_braces.md`,
`have_without_a_proof_is_simp.md` and
`instantiate_without_using_finds_its_guards.md`.

## Acceptance

- `scripts/check.sh` passes, and so does `scripts/check.sh --audit`: `click
  expand` must still rewrite each shortened proof.
- No `by { simp(); }` remains in examples or stdlib.
- The count of `instantiate` calls rewritten, and of those left because their
  list derives a guard, is reported in the pull request.
