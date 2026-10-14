# Refusing a false result after reference calls grows superlinearly

Soundness: not soundness. The false claim is refused at every size; only the
work to refuse it grows too fast. Verifying the true claim stays near
linear.

Checking a proof must cost work roughly linear in the source, the explicit
proof and the state it touches
([verification efficiency](../docs/internals/verification-efficiency.md)).
Refusing a false postcondition after N calls through a reference costs work
that grows faster than quadratically in N, while verifying the true
postcondition of the same function grows about linearly.

Reproduced on master `93bc0b829` with the nightly test
`graph_place_indices_preserve_reference_calls_with_growing_unrelated_places`
in `tests/cpp_import.rs`. It is marked as measuring 34 s and now takes
1,820 s on four cores, almost all of it at N = 64. The C++ caller has N
unused `int` parameters, N `int` locals, and N calls `read(value)`, where
`int read(int& value)` returns `value`:

```cpp
int read(int& value) noexcept { return value; }
int many(int unused0, ..., int unusedN, int& value) noexcept {
    int local0 = 0; ... int localN = N;
    read(value); ... read(value);   // N calls
    return value;
}
```

The sidecar verifies `read`, then claims a false result for `many` and closes
with a simple tactic:

```click
int32 many(int32 unused0, ..., int32& value) {
    owns value; requires value == 7; ensures result == 8; ensures value == 7;
} by { execute(); assumption(); }
```

Wall time per phase, one test at a time on four cores:

| N | import | true claim, `execute(); simp();` | false claim, `execute(); assumption();` |
| --- | --- | --- | --- |
| 8 | 0.24 s | 2.3 s | 8.6 s |
| 16 | 0.20 s | 4.8 s | 29.9 s |
| 32 | 0.32 s | 10.5 s | 201.8 s |
| 64 | | | most of 1,770 s |

Doubling N multiplies the refusal by 3.5, then 6.8, while the true claim
doubles. Both run the same `execute()`, so the extra cost is in the failing
path: the refused `assumption()` and the diagnostic built for it. That is not
yet narrowed further.

Intended regression: a deterministic work-unit curve for the refusal over at
least three sizes of this C++ program, or a C reduction of it, beside the
existing timing test, which stays nightly.

Acceptance: refusing the false claim costs work within a constant factor of
verifying the true one at each size, the curve grows at most linearly in N,
and the nightly test returns near its recorded 34 s.
