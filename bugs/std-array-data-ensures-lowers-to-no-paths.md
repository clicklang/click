# `std::array::data()` result claim lowers to no paths

Soundness: incomplete. A valid proof that the pinned libstdc++
`std::array<int, 4>::data()` returns the address of the array's first element
is refused. The refusal comes from the claim lowering producing no paths; no
false claim is accepted.

Reproduces on master `a9c4dcecc` with a freshly built exporter
(`scripts/build-cpp-exporter.sh`):

```sh
CLICK_CPP_EXPORTER=target/cpp-exporter/click-cpp-exporter RUST_MIN_STACK=8388608 \
  cargo test --test bitcoin_core_money_range -- --ignored --exact \
  axiomatic_std_array_size_and_data_verify
```

The `array-data` case exports

```cpp
#include <array>
int* probe(std::array<int, 4>& a) noexcept { return a.data(); }
```

against the integration's pinned sysroot and verifies

```click
int32* probe(std::array<int, 4>& a) {
    ensures result == &std_array_data(a)[0];
} by { execute(); simp(); }
```

It fails with:

```text
array-data: `probe.contract` path 0, tactic 1: checked outcome `simp` did not
retain a complete transition for every pending claim
`ensures result == &std_array_data(a)[0]` failed for `probe.ensures_0` path 0:
could not lower the claim goal: `probe.contract` proof step tactic 1: could
not lower fixed-state obligation: the kernel lowering produced 0 paths, not one
```

The `array-size` case in the same test passes. The failure is the same when
the test runs alone, so it is not the temporary-directory collision that
makes other tests in this file fail when all of its nightly tests run in
parallel.

Acceptance: `axiomatic_std_array_size_and_data_verify` passes unchanged,
with the harness, the sidecar's claim and the pinned headers as they are.
