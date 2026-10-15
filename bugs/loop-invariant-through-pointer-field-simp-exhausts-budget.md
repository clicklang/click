# A `simp` in the pointer-field loop mdtests exhausts the smart budget

Two nightly mdtests fail on master `e73a38ef2`. A `simp` inside the loop
proof spends the whole smart budget:

```sh
MDTEST_FILTER=loop_invariant_through_loaded_pointer_field CLICK_NIGHTLY=1 \
  cargo test --release --test mdtests
```

```text
verification budget exhausted inside tactic `simp` in `probe_contract.contract`
exhausted its deterministic smart work budget after 2000001 units
(2000000 limit; statement 4, source tactic 12)
```

The same failure occurs in `loop_invariant_through_padded_pointer_field`.
Both are in `NIGHTLY` in `tests/mdtests.rs`, at 10.1 s each, so the gate does
not run them. The breaking commit is not bisected.

The proof fills `j->p[j->lo..j->hi]` in a loop whose invariant quantifies
over the filled prefix, reading every bound through the loaded fields of
`*j`.

The broken invariant: a smart tactic that fails should fail promptly and
locally, not by spending its whole budget. These proofs verified before, so
either a search now explores more than it did, or the proof's state changed
under it.

The same exhaustion fails the nightly lib test
`surface::tests::expansion_tests::padded_struct_field_loop_expansion_reverifies`
(`statement 4, source tactic 12`) on master `26caef84b`, and the nightly
`click audit` reports both mdtests as session failures.

Acceptance:
- Both mdtests verify again on master without raising any budget, with
  their C unchanged.
- If the proof needs a smaller step, the search fails promptly with an
  actionable diagnostic, and the proof is repaired with explicit steps.
