# Wide invariant closure uses an ambient arithmetic search

Simple loop invariants must scale with their declared bundle and explicit
closure, rather than repeatedly searching unrelated proof context.

Reproduced on master `486e809747b79f223ffb2f38ace3034bae9b6491` by:

```sh
cargo nextest run --lib --profile nightly --run-ignored all \
  -E 'test(=surface::tests::scaling_tests::many_clause_bundle_grows_at_most_quadratically)'
```

The fixture retains the original counting loop and adds 2, 4, 8, and 16
invariant declarations `0 - k <= i`. Its deterministic work is 64,401,
33,137, 271,342, and 1,531,740 units. The sharp strategy change at eight
clauses is attributed to `close invariants: direct members` and
`simp closure: indexed bounds`. The last two doublings exceed the existing
quadratic bound. The same test failed in nightly run 38059800813.

Acceptance: the unchanged multi-size regression passes without raising
budgets or weakening its assertions; wide conjunctions retain checked
certificates and loop-specific premise selection; expansion/recheck and
quantified invariant closures still pass.
