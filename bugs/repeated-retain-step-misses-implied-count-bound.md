# A repeated retain step misses a count bound its precondition implies

Soundness: incomplete. A true call precondition is refused; nothing false is
accepted.

The nightly scaling test
`surface::tests::scaling_tests::repeated_retains_of_one_child_scale_with_their_number`
proves `retain_many`, which calls `child_retain(obj)` `count` times. It uses the
shared-heap probe's `child_ref`/`child_control` resources and `child_retain`
verbatim from `design/shared-heap-probes/shared_parent.click`, with:

```click
void retain_many(struct child* obj) {
    requires count(child_ref(obj)) < 2147483643;   // 2147483647 - count, count = 4
    owns child_control(obj);
    owns child_ref(obj);
    produces child_ref(obj);   // repeated `count` times
} by {
    step(child_retain(obj), {});   // repeated `count` times
    step();
    simp();
}
```

The first call step now fails:

```text
4-retain fixture failed: `retain_many.contract` tactic 1: `step()` is missing
prerequisite (precondition clause 1 of `child_retain`):
old(*obj) >= 1 implies old(*obj) + 1 < 2147483647
  C statement at retain.c:12:5: `child_retain(obj);`
  recent premises (showing 8 of 10):
    old(*obj) < 2147483647
    ...
```

`child_retain` requires `count(child_ref(obj)) < 2147483647`, and the caller's
precondition bounds the count well below that. The test passed in the
2026-10-13 nightly (`b5654d4e9`) and has failed since the 2026-10-14 nightly
(`ce7d52ff4`), reproduced on `7f2047bfd`. The fixture is unchanged in that
range apart from `import click::machine_integer;` at the top of
`shared_parent.click`. The test's slice leaves the import out, and adding it
does not change the failure. The single-retain companion
`a_retain_ignores_unrelated_live_children` still passes.

The diagnostic also prints the reference count as `*obj`, which hides what
the prerequisite is about.

Acceptance:

- `repeated_retains_of_one_child_scale_with_their_number` verifies at every
  size again, with near-linear work.
- A refused prerequisite about a population count names the count, not
  `*obj`.
