# Unsigned bound arithmetic produces an invalid addition certificate

## Violated invariant

A smart tactic must emit a kernel-checkable certificate or report a bounded
search failure. This true unsigned bound implication instead reaches the
certificate checker and fails with `signed_int32 addition result does not encode
the child sum`. It was reproduced twice, independently of Rust import or the new
multiplication observation theorem, on 2026-10-07.

## Reproduction and intended regression

Save the following as a Click sidecar and run `click verify`:

```click
theorem lane_ceiling(lane: uint32) {
    requires lane <= 65520u32;
    ensures lane <= 1073741823u32 by {
        arithmetic() using { lane <= 65520u32; }
    }
}
```

The diagnostic points to `arithmetic()` and names the internal signed addition
certificate. This blocks the smart proof of the quotient ceiling for a reduced
Adler-32 lane before multiplying it by four. The explicit existing theorem
`uint32_le_transitive(lane, 65520u32, 1073741823u32)` proves the same implication.

## Acceptance criteria

- Repair the planner/checker encoding mismatch without weakening certificate
  validation or reinterpreting arbitrary unsigned values as signed.
- Verify the reduced proof, profile it, expand it, and reverify its certificate.
- Reject a reversed or insufficient bound, and cover values on both sides of the
  unsigned sign bit.
- Retain deterministic proof-work bounds; do not raise search or wall budgets.
