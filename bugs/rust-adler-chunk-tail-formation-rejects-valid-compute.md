# Rust Adler chunk-tail formation rejects the valid original compute proof

Soundness: incomplete. The pinned, unchanged Rust computation is refused before
its first outer loop. No false claim is known to be accepted. This blocks using
the existing negative controls to assess the separate invariant-search budget bug.

Reproduced on upstream `4b9e21c9f` with the unknown-origin pointer formation
checks in #1373, using the original source, locked import and unchanged proof.
The same original positive check still fails on `acc70c98d` (about 23 seconds):

```sh
cargo nextest run --test rust_import --profile nightly --run-ignored only \
  -E 'test(=adler2_helpers::charon_adler2_general_compute_proves_original_body)'
```

The original positive check fails in about 21 seconds with a proof error:

```text
`__rust_q_I6_adler2_I4_algo_T29___rust_q_I6_adler2_I7_Adler32_I7_compute.contract`
tactic 17: `step()` produced undefined behavior:
pointer arithmetic left the pointed-to object
  operation: `__rust_checked_92 + chunk_iter_remaining`
```

`src/languages/rust/lowering/chunks.rs::chunk_initialize_values` computes this
pointer as the fixed tail of `chunks_exact`: the captured slice pointer plus the
remaining complete-byte count. The input contract holds `views bytes[0u64..bytes_len]`
and bounds the native length by `2147483647u64`. Determine whether the capture
lost pointer-domain evidence or formation checking cannot establish the native
count bound; numeric address equality must not confer another pointer's domain.

The two mutations in
`adler2_helpers::charon_adler2_general_compute_rejects_false_b_specification`
also both stop at this exact early operation. That negative test currently
passes because `reject_compute` accepts any non-budget proof error. Its passing
result therefore does not resolve
[`adler-general-false-b-invariant-exhausts-smart-budget.md`](adler-general-false-b-invariant-exhausts-smart-budget.md).
On master `925c21651`, the seed mutation instead reached outer-loop invariant 37
and exhausted its unchanged two-million-unit entry-planning budget.

Acceptance:

- Preserve the original Rust program, pinned import and valid contract.
- Restore the original positive general-compute proof and independent checking
  of its complete expanded certificate.
- Preserve formation rejection for unrelated origins and out-of-bounds offsets.
- Check that both existing false-B mutations reach their intended invalid
  obligations and are refused below the unchanged work limit; do not treat
  this earlier undefined-behavior refusal as evidence of a budget fix.

This report overlaps the pointer-domain work and is left for that thread;
no verifier or Rust-lowering workaround was applied during diagnosis.
