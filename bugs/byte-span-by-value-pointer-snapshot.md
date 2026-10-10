# A by-value span wrapper loses its pointer-identity proof across snapshots

## Violated invariant

A trivial descriptor copy preserves its backing pointer. A wrapper taking
`std::span<int>` by value and returning `std::as_writable_bytes(span)` should
prove that pointer identity, under the catalog's explicit assumed contract.
The corresponding const-reference wrapper proves it, but the by-value wrapper
currently fails. No backing storage is read or written by either wrapper.

## Reproduction

`pinned_writable_byte_span_by_value_snapshot_gap_is_bounded` in
`tests/bitcoin_core_money_range.rs` builds this unchanged source against the
pinned Bitcoin Core/libstdc++ closure, then verifies offline:

```cpp
#include <span.h>
std::span<std::byte> probe(std::span<int> span) noexcept {
    return std::as_writable_bytes(span);
}
```

```click
verifying "span-probe.cpp";
struct span__std_byte__value_unsigned_long_18446744073709551615
probe(struct span__int__value_unsigned_long_18446744073709551615 span) {
    ensures std_span_data(result) == old((uint8*)std_span_data(span));
    ensures std_span_size(result) == old(std_span_size(span)) * 4u64;
} by { execute(); simp(); }
```

With the pinned exporter built and `CLICK_CPP_EXPORTER` pointing to it, run
`cargo nextest run --test bitcoin_core_money_range --run-ignored all --no-capture -E
'test(pinned_writable_byte_span_by_value_snapshot_gap_is_bounded)'`.
The test currently asserts the bounded refusal; change it to the positive
`check_pinned_byte_proof` assertion when repairing the defect.

Execution completes, but simplification refuses `probe.ensures_0` with
“the two sides read the same address in different memory snapshots”. Both
current-field and entry-field formulations have reproduced the pointer failure.
A focused `with_proof_trace("probe", ...)` capture at the failing step
currently reports only “no checked simple steps recorded on this path”; it
provides neither the decisive pointer comparison nor its snapshot transport.
The test prints that trace with `--no-capture`. This does not establish an
underlying cause: investigate trace coverage and the comparison before further
local proof variations. The ordinary diagnostic supplies the snapshot mismatch
quoted above.

The independent reference fixture proves address, length, and unchanged input
fields with ordinary, expanded, and retained certificates. Its field-view
requirements are essential and must remain checked.

## Intended regression and acceptance criteria

- Preserve the by-value C++ source and its general true contract above.
- Make the focused trace expose the failed pointer comparison and the relevant
  checked call/entry facts, rather than an empty path.
- Prove pointer and length relations ordinarily, after expansion, and with
  retained certificates, using checked snapshot/value transport.
- Keep actual aggregate argument reads subject to source read permission and
  initialization; entry values must not grant backing ownership.
- Continue refusing incorrect pointer offsets, incorrect byte lengths, and
  reads of backing storage without permission.
- Keep the proof bounded and add deterministic scaling coverage if repairing
  transport changes a verifier hot path. Delete this bug file with the fix.
