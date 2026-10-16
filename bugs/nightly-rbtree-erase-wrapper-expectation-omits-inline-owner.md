# The erase-wrapper mutation expects an unqualified inline helper diagnostic

Priority: P2.

Soundness: not soundness. The verifier correctly refuses the changed C wrapper;
the nightly regression fails because its expected diagnostic omits the inline
function's source-owner suffix.

## Reproduction

Run the existing mutation test against master plus PR #1238:

```sh
cargo nextest run --test examples --profile nightly --run-ignored only \
    -E 'test(=rbtree_erase_wrapper_requires_nonnull_color_repair)'
```

In `tests/examples.rs`, this changes `if (rebalance)` to `if (!rebalance)` in
`examples/rbtree-erase/rb_erase.c`. The proof correctly refuses the skipped
repair call, reporting:

```text
requires a call to `____rb_erase_color#inline:rb_erase.c` at the current frontier; next operation: skip
```

The assertion instead requires:

```text
requires a call to `____rb_erase_color` at the current frontier
```

Reproduced with the existing example test binary on 2026-10-16; the mutation is
rejected in about 12 seconds, then the diagnostic assertion panics. This is
independent of the fixture performance reductions.

## Acceptance

- Recognize the intended inline helper and skipped-call frontier in the
  diagnostic, keeping the mutation and rejection assertion meaningful.
- The named nightly regression passes; the unchanged C wrapper remains the
  positive integration control.
