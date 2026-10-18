# Outcome resource unfold rejects an equivalent published state

Soundness: incomplete. A valid post-execution unfold/fold of an owned pure
resource is rejected because its resource facts have a different internal
representation. No false claim was accepted in this reproduction.

Reproduced with production at 1502dd900 and unchanged tests at
eda32be9f3c27e72f2c171a75c3ceb47532ef22c, Rust 1.98.1, ordinary unoptimized
lib test profile:

```sh
RUST_MIN_STACK=8388608 cargo test --lib \
  surface::tests::scaling_tests::outcome_haves_and_resource_folds_do_not_reimport_ambient_facts \
  -- --exact --include-ignored --nocapture
RUST_MIN_STACK=8388608 cargo test --lib \
  surface::tests::scaling_tests::authority_outcome_haves_and_resource_folds_do_not_reimport_ambient_facts \
  -- --exact --include-ignored --nocapture
```

Both unchanged tests fail at ambient=8, operations=1 in their shared helper.
The former uses verify_c0_sources; the latter uses verify_c0_project. The
zero-operation control verifies. The relevant generated source is:

```c
int32 identity(int32 x) { return x; }
```

```click
resource marker(x: int32) { fact x == x; }
verifying "identity.c";
int32 identity(int32 x) {
    requires x != 0; requires x != 1; requires x != 2; requires x != 3;
    requires x != 4; requires x != 5; requires x != 6; requires x != 7;
    owns marker(x);
    ensures result == x;
} by {
    execute();
    have 1000 == 1000 by { normalize(); }
    unfold(marker(x));
    fold(marker(x));
    simp();
}
```

The unchanged tests report:

```text
identity.contract proof step tactic 2:
return composite exchange has a different published state:
the resource facts are held in a different representation
```

Acceptance: both original matrix tests must reach all their existing size and
operation-count checks, retaining the exact fact-entry delta assertions.
The valid completed-path unfold/fold must not require the producer's known
state to have a particular storage representation. Preserve the native C,
pure resource, and post-execution have; do not remove the outcome operations
or weaken the entry-count bounds to bypass this rejection.
