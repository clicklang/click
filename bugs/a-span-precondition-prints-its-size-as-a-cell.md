# A span precondition after execution prints its size as a cell

Soundness: sound. The failure is in how a refusal is printed. Nothing is
accepted that should not be: the obligation is the right one and is refused.

## Violated invariant

Diagnostics print a C++ standard-library model through its accessor, as
`std_span_size(s)`, and never through the library's layout (see
[the C++ standard library](../docs/reference/cli/import.md#c-standard-library)).
When `execute()` reaches a catalog call whose precondition mentions the
receiver's size, the missing-prerequisite message prints that size as a raw
cell of the reference carrier, `at(<state A>, &s[2])`. Here `&s[2]` is the
`int32` cell at byte offset 8 of the `std::span`, which is libstdc++'s
`_M_extent._M_extent_value`. The reader sees neither the accessor nor a field
name, so a proof author cannot tell which value the obligation is about.

## Reproduction

With the pinned Bitcoin Core fixture (`pinned_span_fixture_with_exact_dependencies`
in `tests/bitcoin_core_money_range.rs`) and dependencies
`sysroot/usr/include/c++/12/span` and
`sysroot/usr/include/x86_64-linux-gnu/c++/12/bits/c++config.h`, the harness is:

```cpp
#include <span>
std::span<int> probe(std::span<int>& s) noexcept { unsigned long n = s.size(); return s.first(n - 1); }
```

The sidecar omits the nonempty precondition:

```click
verifying "span-probe.cpp";
struct span__int__value_unsigned_long_18446744073709551615 probe(struct span__int__value_unsigned_long_18446744073709551615& s) {
    views std_span_data(s);
    views std_span_size(s);
    ensures std_span_data(result) == std_span_data(s);
} by { execute(); simp(); }
```

Verification is refused with:

```text
`probe.contract` tactic 0: `execute()` is missing prerequisite
(span__int__value_unsigned_long_18446744073709551615_first precondition):
condition-certificate premise search did not derive `n - 1u64 <= at(<state A>, &s[2])
```

`std::span<unsigned char>` prints the same cell, and so do `last` and
`subspan`.

## Acceptance criteria

- The refusal above prints the receiver's size as `std_span_size(s)`, and the
  data pointer as `std_span_data(s)` where it appears.
- A regression in `tests/bitcoin_core_money_range.rs` asserts the accessor
  spelling, and asserts that no `&s[` cell spelling appears, for a catalog
  precondition reached by `execute()`.
