# Write the Adler sidecars in Rust syntax, then refuse the C-shaped spelling

Priority: P1.

A Rust sidecar looks like Rust (decided 2026-10-08). The active Adler
contracts use Rust signatures, paths, methods, slices, fields, casts, and short
proof forms. Click still accepts the older C-shaped function spelling for a
Rust source; remove that compatibility.

## Violated invariant

One thing has one spelling. For a Rust source, the contract of a function
is written as Rust writes its signature, and only that way.

## Work

Refuse the C-shaped spelling for a Rust source:
- the parser refuses a C-shaped signature and `->` in a sidecar whose
  source is `.rs`, naming the `fn` spelling to write;
- `a_rust_sidecar_states_its_signature_in_rust_syntax` in
  `src/surface/tests/surface_syntax.rs` compares the two spellings
  today; it becomes the refusal's test;
- `docs/reference/rust.md` drops the sentence accepting the C-shaped
  spelling, and the compatibility note in the Adler README goes.

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
