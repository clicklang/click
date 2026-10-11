# Write the Adler sidecars in Rust syntax, then refuse the C-shaped spelling

Priority: P1.

A Rust sidecar looks like Rust (decided 2026-10-08). Every Rust sidecar in
the repository is written that way except the ones under
`design/charon-trial/adler2/`, which still use the C-shaped spelling: C
types and parameter lists, the importer's names
(`__rust_q_I6_adler2_I4_algo_I5_U32X4`), `->`, an explicit `bytes_len`, and
the long proof forms. While they do, Click has to accept both spellings
for a Rust source, so a Rust sidecar can still be written two ways.

## Violated invariant

One thing has one spelling. For a Rust source, the contract of a function
is written as Rust writes its signature, and only that way.

## Work

1. Convert each Adler sidecar to Rust syntax (`docs/reference/rust.md`,
   "Signatures in Rust syntax"):
   - `fn` signatures with Rust types: `fn adler32_slice(data: &[u8]) -> u32`;
   - methods in `impl` blocks with `self`, `&self` or `&mut self`;
     operator methods as trait impls, `impl MulAssign<u32> for U32X4`;
   - items by path: `adler2::algo::U32X4`, `adler2::Adler32::compute`;
   - a slice as one name, `bytes.len()` and `*bytes`, with no `bytes_len`;
   - fields through a reference as `p.f`, not `p->f`; casts as `x as u32`;
   - the short proof forms: `have P;` for `have P by { simp(); }` and
     `by T(args);` for a one-step proof.

   The tests in `tests/rust_import/adler2_helpers.rs` cut `helpers.click`
   apart by its text and pass `--claim` with importer names. Update them in
   the same change; `--claim` and `--trace-proof` already accept the Rust
   path (`adler2::Adler32::compute.contract`).

2. Then refuse the C-shaped spelling for a Rust source, in its own change:
   - the parser refuses a C-shaped signature and `->` in a sidecar whose
     source is `.rs`, naming the `fn` spelling to write;
   - `a_rust_sidecar_states_its_signature_in_rust_syntax` in
     `src/surface/tests/surface_syntax.rs` compares the two spellings
     today; it becomes the refusal's test;
   - `docs/reference/rust.md` drops the sentence that keeps the C-shaped
     spelling until the Adler sidecars are converted, and the note in
     `design/charon-trial/adler2/README.md` goes.

Not converted: the five hash-pinned originals listed in
`design/charon-trial/parity.json`, and `into-slices/sum.click`, which a test
compares byte for byte with one of them. The refusal has to leave those
readable, for example by checking them as frozen inputs.

## Regression

- A Rust sidecar with `uint32 f(const uint8* bytes, uint64 bytes_len)` is
  refused, and the message names `fn f(bytes: &[u8]) -> u32`.
- A Rust sidecar with `p->f` is refused, naming `p.f`.
- The Adler nightly tests pass on the converted sidecars.

## Done when

No Rust sidecar outside the frozen originals is C-shaped, the parser
refuses the C-shaped spelling for a Rust source, and the documentation
describes one spelling.

Related: `bugs/adler-small-batch-audit-rewrite-exceeds-parenthesis-depth.md`
(the audit of the small-batch compute claim, on master before this work).
Still printed as the kernel spells it, outside this issue: a kernel term in
a proof context (`load(bytes)`, `UInt64From32(x)`), and an operator method's
importer name in a label.
