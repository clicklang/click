# Returned construction loses a composed observer's value relation

At `67d36e1aed2fcc80b8cc56d905dba53a71772942` (PR 646), the existing
`returned_constructor_composed_observers_verify_and_reject_writes_offline`
C++ integration test fails. This reproduces in PR CI and in a fresh local build.

## Reproduction

With the pinned C++ exporter configured:

```console
cargo nextest run --test cpp_import -E 'test(returned_constructor_composed_observers_verify_and_reject_writes_offline)'
```

Keep the source and contracts embedded in `tests/cpp_import.rs`. The fixture
constructs a returned `Box` from a composed observer of a referenced `Count`.
Its exact result claim is `result.value == count.value + 1u64`, and it retains
the input field with `count.value == old(count.value)`.

The result claim fails at `probe.contract` tactic 1. The diagnostic reports
that a call may have changed the read and that the written ranges have not
been shown separate. The constructor/input-read regression recorded in
[Raw construction destinations hide initialized constructor inputs](raw-construction-destination-hides-initialized-input.md)
is adjacent, but a shared root cause has not been established.

## Invariant and acceptance

The selected construction-return profile must preserve the semantics of the
original composed observer and its checked call sequence, including the precise
aliasing admitted by the source and contract. It must not gain freshness merely
because a result destination is involved.

Investigate the proof-entry value naming, argument capture, destination binding
and checked frame evidence. Restore the original exact result and frame claims
through ordinary, expanded and retained verification, including the fixture's
negative mutation checks. If the source profile itself lacks necessary admission
evidence, report that specifically instead of inventing a kernel separation
fact. Do not replace the claim with safety alone or add proof-only source changes.
