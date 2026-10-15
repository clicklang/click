# A wide store index past the difference graph's edge limit leaves its object

Soundness: incomplete. A true bound stops being derivable; nothing false is
accepted.

The nightly scaling test
`surface::tests::scaling_tests::stores_to_bounded_unordered_size_t_indices_are_near_linear`
stores to `a[ck]` for `N` `uint64` indices, each bounded only by
`requires ck < n;`, beside `owns a[0..n];`. It verifies at `N` = 4, 8, 16 and
32 and fails at 64 on the 33rd store:

```text
64 bounded size_t-index stores should verify: `mark.contract` tactic 32:
`step()` produced undefined behavior: pointer arithmetic left the pointed-to object
  operation: `a + c32`
  C statement at mark.c:34:5: `a[c32] = 32;`
  pure facts: [true, c0 < n, c1 < n, ..., … 55 more omitted]
```

`c32 < n` is a written precondition. It passed in the 2026-10-13 nightly
(`b5654d4e9`) and has failed since the 2026-10-14 nightly (`ce7d52ff4`),
reproduced on `7f2047bfd`. That range includes `d6298e9cc` ("Bound the
difference graph's propagation and consult it from decide"). That change pushes a
bound along at most `EDGE_LIMIT` edges (`src/kernel/difference_graph.rs`,
`EDGE_LIMIT = 32`) and says that "past the limit the graph stays sound and
answers less". The first failing index is the 33rd dependent of the shared
bound `n`, which suggests the wide membership rule no longer finds a
precondition once its hub has more than `EDGE_LIMIT` dependents.
The int32 companion `stores_to_bounded_unordered_indices_are_near_linear` and
the order-walk scaling tests fail in the same range, possibly from the same
cause.

Acceptance:

- A store `a[ck]` whose index has a written `ck < n` stays inside
  `owns a[0..n]` however many other indices `n` bounds.
- `stores_to_bounded_unordered_size_t_indices_are_near_linear` passes at all
  its sizes, with near-linear store work.
