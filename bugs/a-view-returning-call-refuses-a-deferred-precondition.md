# A view-returning call refuses a precondition it would discharge later

Soundness: sound. The defect refuses provable calls and names the wrong
kind of obligation. Nothing false is accepted.

## Violated invariant

A call's precondition that holds on the path should be accepted whatever
shape the callee contract states it in. Plain C behaves this way: a call
whose precondition is a disjunction or an implication is accepted when the
path proves it.

A C++ call that returns a record viewing its receiver, as
`std::span<T>::subspan` does, goes through stable-view recovery in
`recover_candidate_stable_view_resources` (`src/kernel/functions.rs`).
Recovery fails closed while any obligation is pending, and a precondition
that is not discharged on the spot is pending. So a provable call is refused
with:

```text
function contract could not be applied: stable-view call has an undischarged return obligation
```

The message calls it a return obligation, but the pending obligation is the
call's precondition. `--trace-proof` does not show which obligation is
pending.

## Reproduction

The catalog's `std::span<T>::subspan(offset, count)` contract
(`src/languages/cpp/standard_library.rs`) requires
`count != std::dynamic_extent implies count <= size - offset`. With the pinned
Bitcoin Core span fixture (`axiomatic_span_fixture` in
`tests/bitcoin_core_money_range.rs`) and dependencies
`sysroot/usr/include/c++/12/cstddef`, `sysroot/usr/include/c++/12/span` and
`sysroot/usr/include/x86_64-linux-gnu/c++/12/bits/c++config.h`:

```cpp
#include <span>
std::span<std::byte> probe(std::span<std::byte>& s) noexcept { return s.subspan(1, std::dynamic_extent); }
```

```click
verifying "span-probe.cpp";
struct span__std_byte__value_unsigned_long_18446744073709551615 probe(struct span__std_byte__value_unsigned_long_18446744073709551615& s) {
    views std_span_data(s);
    views std_span_size(s);
    requires 1u64 <= std_span_size(s);
    ensures std_span_data(result) == std_span_data(s) + 1u64;
    ensures std_span_size(result) == std_span_size(s) - 1u64;
} by { execute(); simp(); }
```

`execute()` refuses the call with the message above, although the
precondition's antecedent `18446744073709551615u64 != 18446744073709551615u64`
is false.

The two equivalent precondition forms fail on opposite calls:

| Precondition form | `subspan(1, 2)`, after a fact `2 <= size - 1` | `subspan(1, std::dynamic_extent)` |
| --- | --- | --- |
| `count != MAX implies count <= size - offset` | verifies | refused |
| `count == MAX or count <= size - offset` | refused | verifies |
| `count <= size - offset or count == MAX` | refused | verifies |

Both forms verify for both callers in plain C, with
`uint64 window(uint64 size, uint64 offset, uint64 count)` stating the same
precondition and calls `window(size, 1, 2)` and
`window(size, 1, 18446744073709551615u)`.

## Acceptance criteria

- The reproduction verifies with the catalog contract unchanged, and so does
  `subspan(1, 2)` (already covered by
  `axiomatic_span_subviews_and_byte_size_verify_for_other_elements`).
- A call whose precondition is false is still refused, naming the
  precondition.
- If a pending obligation still blocks recovery, the refusal names it as a
  precondition, prints it, and `--trace-proof` shows it.
- Restore `std::dynamic_extent` coverage in
  `axiomatic_span_byte_element_entries_verify`.
