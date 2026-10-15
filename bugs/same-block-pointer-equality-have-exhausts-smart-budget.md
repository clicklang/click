# A same-block pointer equality `have` exhausts the smart budget

Soundness: not soundness. A smart `have` that used to close now runs out
of its deterministic budget and the proof is refused. Nothing false is
accepted; this is a performance and completeness regression in smart
search.

Since `c0cf00874` ("Preserve pointer comparison evidence across equivalent
address spellings", merged in #1044 as `c819a273e`), the adler2 four-byte
compute proof fails in its loop's `preserve` body. Line 126 of
`design/charon-trial/adler2/four-byte-compute.click` is

```click
have __rust_mir_62_cursor == old(bytes);
```

with the invariant `__rust_mir_62_cursor == old(bytes) + (4 - ((__rust_mir_62_remaining as u32) as i32))`
and the line before it proving `((__rust_mir_62_remaining as u32) as i32) == 4`
in context. The implicit `auto` behind the `have` charged 192,075 units on
`b9287e862`, the parent of `c0cf00874`. On `c0cf00874` and on master
`7f2047bfd` it exceeds the 2,000,000-unit smart budget (4.4 s):

```text
verification budget exhausted inside tactic `have` in `adler2::Adler32::compute.contract`
exhausted its deterministic smart work budget after 2000001 units
(2000000 limit; statement 904, source tactic 58)
  open operation spans
  `simp closure: indexed goal equality rewrite` (1997707 units in) >
  `simp premise surface at recorded snapshots` (538067 units in)
  top completed operation work
  1144108 `simp premise surface at recorded snapshots`,
  311923 `simp premise surface across recorded snapshots`, ...
goal: __rust_mir_62_cursor == bytes
```

So almost all the work goes into spelling premises at the proof's recorded
snapshots for the indexed goal-equality rewrite. That commit stopped
`ConditionTerm::pointer_equal` from reducing a same-block comparison to
`PointerOffsetEqual`. The fact and the goal are now `PointerEqual` terms,
and the equality graph derives their offset view. A likely cause is that the
rewrite's candidate equalities, or the premise surfacing for those
candidates, now take a path that tries every recorded snapshot without
finding a spelling. This has not been confirmed by a trace.

Three nightly tests fail on this one `have`:
`charon_adler2_four_byte_compute_proves_original_body_and_rejects_false_outputs`,
`charon_adler2_four_byte_compute_tools_recheck_original_contract` and
`charon_adler2_public_boundaries_tools_check_all_original_bodies`. The last
one fails inside `click profile`.

The violated invariant is that a smart tactic that fails should fail
promptly and locally rather than spend its whole budget
([proof-failure triage](../docs/concepts/proof-failure-triage.md)). Also, a
representation change must not make a previously closing search cost
more than ten times as much.

## Reproduction

```sh
RUST_MIN_STACK=8388608 CLICK_NIGHTLY=1 \
CLICK_CHARON=$PWD/target/charon/debug/charon \
  cargo nextest run --test rust_import --run-ignored all --profile nightly \
  -E 'test(charon_adler2_four_byte_compute_proves_original_body_and_rejects_false_outputs)'
```

It takes about 30 s. To get the CLI form, copy the project that
`compute_project(FOUR_BYTE_COMPUTE)` writes in
`tests/rust_import/adler2_helpers.rs` out of the test's temporary directory.
Then run `CLICK_TIMINGS=1 click verify <copy>/borrow.click`, with an absolute
path, to get the attribution above.

No reduced reproduction exists yet. The intended regression keeps the
original shape: a Rust slice cursor `cursor == base + (4 - k)` held as a
loop invariant, with `k == 4` proved before a `have cursor == base` in the
loop's `preserve` body. That `have` sits behind enough recorded snapshots
(calls and `mark`s) that per-snapshot premise spelling is expensive.
The separate pointer-field loop budget failures were repaired by explicitly
instantiating their filled-prefix fact after the increment; that proof repair
does not address this cursor equality search.

## Acceptance criteria

- The three nightly tests above pass on master without raising any budget
  and without changing the adler2 Rust source or the proof's claims.
- The `have` costs no more than it did on `b9287e862` (192,075 units), or
  a smaller explicit step replaces it and the smart search fails promptly
  with an actionable diagnostic.
- A deterministic regression covers same-block pointer equality goals
  closed from an offset-shifted pointer equality fact: one beside a growing
  number of recorded snapshots, and one checking that the
  premise-surfacing work does not grow with them.
