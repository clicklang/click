# zlib sixteen-byte block `step` exhausts the simple work budget

Soundness: incomplete. A committed proof of zlib's `adler32_z` sixteen-byte
block path stops with a work-budget refusal inside one `step`. Nothing false
verifies; the proof is refused.

Reproduces on master `1502dd900`:

```sh
cargo run --bin click -- verify design/charon-trial/zlib/sixteen.click
```

```text
proof error:
  verification budget exhausted inside tactic `step` in `adler32_z.contract`
  exhausted its deterministic simple work budget after 750001 units
  (750000 limit; statement 165, source tactic 208)
```

The nightly test `pinned_zlib_sixteen_block_matches_checked_shared_specification_offline`
in `tests/compiler_import.rs` fails the same way. The other zlib sidecars in
`design/charon-trial/zlib/` and their nightly tests pass.

A slow simple tactic is a Click engine defect, not a proof to rewrite: the
`step` must stay within the simple budget (see
`docs/internals/verification-efficiency.md`). Profile it with
`click profile` or `CLICK_TIMINGS=1` to find where the units go.

Acceptance: `sixteen.click` verifies unchanged, with the same unchanged
`adler32.c`, and its nightly test passes, without raising the budget.
