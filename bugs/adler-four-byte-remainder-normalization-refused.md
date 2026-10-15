# Adler four-byte reduction refuses a remainder normalization

Soundness: incomplete. The original Rust checksum proof is rejected at a
remainder equality after its pointer equality has been checked. No false
acceptance is demonstrated.

The unchanged `design/charon-trial/adler2/four-byte-compute.click`, assembled
by `compute_proof(FOUR_BYTE_COMPUTE)` in `tests/rust_import/adler2_helpers.rs`,
reaches this proof at the first lane's final `b` reduction:

```click
have __rust_checked_81 == 65521u32;
have b_vec.0[0] == at(reduction_b, b_vec.0[0]) % __rust_checked_81
    by simp() using { b_vec.0[0] == at(reduction_b, b_vec.0[0]) % __rust_checked_81; };
have b_vec.0[0] == at(reduction_b, b_vec.0[0]) % 65521u32 by {
    rewrite(b_vec.0[0] == at(reduction_b, b_vec.0[0]) % __rust_checked_81);
    simp() using { __rust_checked_81 == 65521u32; }
}
```

The selected `simp` refuses this goal (the diagnostic's state A is a
memory derived from another state for one read):

```text
at(<state A>, __rust_mir_86[__rust_mir_111_live]) % __rust_checked_81
 == at(<state A>, __rust_mir_86[__rust_mir_111_live]) % __rust_checked_81 % 65521u32
```

This was hidden behind the earlier same-block pointer equality budget
failure. It is also reproduced when that equality alone is replaced by
the two explicit checked rewrites of the cursor invariant and the proved
remaining-count equality. The explicit pointer proof costs 402 units and
does not change the Rust source, contracts, or later reduction proof.
The automatic pointer-search repair reaches the same refusal without
changing the original proof.

Reproduce with the named nightly Rust import tests (run individually,
without enabling the entire nightly suite):

- `adler2_helpers::charon_adler2_four_byte_compute_proves_original_body_and_rejects_false_outputs`
- `adler2_helpers::charon_adler2_four_byte_compute_tools_recheck_original_contract`
- `adler2_helpers::charon_adler2_public_boundaries_tools_check_all_original_bodies`

The checked cursor-site work regression is independent of the full-body
verdict; it must not be treated as evidence that the complete proof passes.

Acceptance:

- Attribute the refusal with a reduced checked-state reproduction, retaining
  the original memory-read/snapshot pattern if it is material.
- The original four-byte computation and public-boundary assemblies verify,
  expand, reverify, and pass their named tool checks, without changing the
  Rust source, weakening claims, or increasing budgets.
- Reject a wrong modulus and a false remainder equality.
