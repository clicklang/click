# General Adler computation cannot finish its selected-claim audit

On master `486e8097`, the nightly test
`adler2_helpers::charon_adler2_general_compute_tools_recheck_original_contract`
verifies and profiles the original contract, then fails at `audit --claim`.
The audit reaches its existing ten-minute run bound without completing any
of the 765 selected smart sites. A separate reproduction with no other proof
checks running has the same result; session initialization takes 132 seconds
and expansion/checking consumes the remaining run time.

Reproduce using the unchanged `compute_proof(GENERAL_COMPUTE)` fixture from
`tests/rust_import/adler2_helpers.rs` and its locked native input, or run:

```sh
CLICK_NIGHTLY=1 cargo nextest run --test rust_import --profile nightly \
  --run-ignored all -E 'test(charon_adler2_general_compute_tools_recheck_original_contract)'
```

Acceptance: the selected whole computation audit and subsequent expansion
and verification pass within the existing limits, without skipping sites,
weakening the contract, or changing the Rust input. Protect any checking
optimization with a focused deterministic scaling regression.
