# Audit of the Adler small-batch compute claim writes a sidecar it cannot parse

`click audit` must rewrite a claim's smart sites into simple certificates
that parse and verify. On the Adler small-batch compute contract the batch
rewrite produces source that the parser refuses:

```text
CLAIM [1/1] borrow.click  __rust_q_I6_adler2_I4_algo_T29___rust_q_I6_adler2_I7_Adler32_I7_compute.contract (510 sites) ... FAIL
    could not locate `...compute.contract` in the rewritten sidecar:
    borrow.click:6657: parenthesis nesting exceeds Click's supported depth of 16
```

Reproduction: the nightly test
`adler2_helpers::charon_adler2_small_batch_compute_tools_recheck_original_contract`
in `tests/rust_import/adler2_helpers.rs` (about 8 minutes, needs the pinned
Charon: `CLICK_CHARON=target/charon/debug/charon RUST_MIN_STACK=8388608`).
It assembles `design/charon-trial/adler2/small-batch-compute.click` with the
helpers and runs `verify`, `profile`, then
`audit --claim <compute>.contract`, which fails as above. Reproduced on
2026-10-11 at master `c5b25806`; `verify` and `profile` pass.

The rewritten sidecar is a temporary file the audit does not keep. Start by
writing it out (or running `click expand --claim` on the same claim) and
reading line 6657: either the printer nests a term more deeply than the
parser accepts, or a printed term needs fewer parentheses than it gets.

Also reproduced on master `486e8097` with a small theorem: a flat sum of
24 occurrences of an Integer parameter `a`, asserted equal to `24 * a`
in a `have ... by { arithmetic(); }`, verifies. Expanding that arithmetic
site fails with the same parenthesis-depth diagnostic. The source printer
adds one parenthesis pair at every left-associated addition node.
The full Adler claim still fails in `click expand` at line 6745.

Acceptance:

- the printer and the parser agree: whatever `click expand` and the audit
  batch rewrite print, the parser reads back, or the expansion is refused
  with a prompt, local diagnostic naming the claim and the term;
- a small regression (an mdtest or unit test) with a term at the depth
  that fails here, printed and parsed back;
- the nightly test above passes.
