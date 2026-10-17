# Nightly loop-view partition fixture fails before its scaling assertion

Soundness: not soundness. An existing nightly regression fails while constructing
its expected successful resource partition. No false claim is accepted. The
fixture's pointer-carrier assumptions need to be checked before treating this as
a verifier rejection of valid input.

Reproduced on upstream `37346c387` with the unchanged test:

```sh
cargo test --lib \
  kernel::loops::v10_tests::scaling_tests::loop_view_partition_uses_alias_graph_without_scanning_ambient_ranges \
  -- --exact --ignored --nocapture
```

The test in `src/scaling_tests/kernel/loops/v10_tests.rs` owns eight bytes at
symbolic pointer 916100, records that pointer 916101 equals its two-byte offset,
and requests a four-byte loop view through a `uint8*` local holding 916101. At
the first size (16 unrelated ranges),
`loop_declared_and_withheld_resources` returns `Unheld` for that view. The
`.unwrap()` at line 65 panics, before the partition, missing-equality negative
control, or scaling assertions run.

The diagnostic shows different carrier metadata: the held range has
`typed_carrier: false` and an opaque extent rooted at 916100; the requested view
has `typed_carrier: true` and an opaque extent rooted at 916101. Numeric address
equality alone may not supply the intended origin/designation evidence.

Acceptance criteria:

- Establish whether the fixture supplies the pointer-origin and carrier
  evidence required by the current resource semantics. Correct its construction
  if that evidence is missing; otherwise fix the rejection.
- Preserve the selected interior-alias view, unrelated ranges, expected kept
  owner, and rejection when the alias premise is absent.
- Make the named regression pass through its existing scaling assertions;
  do not relax resource identity or provenance checks to silence the fixture.
