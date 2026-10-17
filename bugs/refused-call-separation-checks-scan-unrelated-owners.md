# Refused call-separation checks scan unrelated owners

Soundness: not soundness. The unestablished separation is correctly refused;
the defect is that its requirement-checking work grows with unrelated owned
objects. No false proof acceptance was observed.

Reproduced with production `1171662cb5785654c295e5f60f29c7d861d25895`, Rust
1.98.1, and the unmodified body of
`surface::tests::scaling_tests::call_separation_requirements_ignore_unrelated_owned_objects`.
The exact named test fails at its refused-work assertion:

```sh
RUST_MIN_STACK=8388608 cargo test --lib \
  surface::tests::scaling_tests::call_separation_requirements_ignore_unrelated_owned_objects \
  -- --exact --ignored --nocapture
```

For 2, 4, 8, and 16 unrelated objects, the captured work is:

```text
proved  [100, 100, 100, 100]
guarded [246, 246, 246, 246]
refused [3847, 6591, 12079, 22910]
```

The test is in `src/scaling_tests/surface/tests/scaling_tests.rs`. It captures
`operation verified call requirement checking`, not total parsing or fixture
setup. The caller owns `a->left` and `b->size`, plus `qN->left` and `qN->size`
for each unrelated pointer parameter. The callee's refused requirement is
`separate(memory(a->left), memory(b->left))`; nothing establishes that
separation. All cases reject, but refusal walks the unrelated frame. The
established `a->left`/`b->size` separation and the null-guarded control retain
constant work.

A simple call requirement's unsuccessful reasoning must inspect its selected
operands and indexed evidence, rather than every unrelated owner. Investigate
the refusal path and its failure-evidence collection; the passing controls
already demonstrate bounded successful checking.

Acceptance criteria:

- Restore the existing named regression with its refused, proved, and guarded
  cases retained. Do not relax its bounds or remove the refusal assertion to
  obtain a pass.
- Keep the unestablished separation refused and both positive controls valid.
- Make refused requirement-checking work independent of the number of
  unrelated owned objects, subject only to the documented indexing factors.
