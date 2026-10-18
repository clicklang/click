# A verified C++ boolean member cannot write its complete certificate

Soundness: incomplete. The original `FeeRateState::IsEmpty` proof verifies, and
its selected-tactic expansion checks, but formatting its already checked
whole-claim certificate refuses a surface/frame path mismatch. No false claim
is known to verify.

Priority: P2.

## Reproduction

Reproduced on production `7a635bb004b68a547a3f3ec9b066cc6ad32a3691`, using
LLVM/Clang 19.1.7 and the ordinary unoptimized Rust test profile.

Keep the original sources:

- `tests/fixtures/cpp-verification/class-record/class_record.cpp`
- `tests/fixtures/cpp-verification/class-record/is_empty.click`

The native method is `bool IsEmpty() const noexcept { return size == 0; }`.
The sidecar views both fields, preserves both values, and proves the boolean
result with `execute(); simp();`. The unchanged integration test
`class_records_preserve_private_and_protected_field_layout_and_authority`
passes, including the private/protected/public variants and the other methods.

To reproduce inside `tests/cpp_import.rs`, where the existing `Project` helper
sets up the pinned compiler import:

```rust
#[test]
fn class_bool_whole_certificate_reproduction() {
    let project = Project::with_fixture(
        "class_record.cpp",
        "FeeRateState::IsEmpty",
        include_str!("fixtures/cpp-verification/class-record/class_record.cpp"),
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = include_str!("fixtures/cpp-verification/class-record/is_empty.click");
    let path = project.directory.join("original.click");
    fs::write(&path, source).unwrap();
    let parsed = read_click_project(&path, source).unwrap();
    let sites = project_smart_tactic_source_sites(
        &parsed, &ProgramInputs::program(&import),
    ).unwrap();
    let claim = sites[0].claim_label.clone();
    let (_session, verified) =
        C0VerificationSession::new_program_prepared_project(&parsed, &import).unwrap();
    click::surface::expand_verified_function_claim_source_by_label(
        source, &verified, &claim,
    ).unwrap().expect("the checked claim is declared in this source");
}
```

Build the exporter with `scripts/build-cpp-exporter.sh`, set
`CLICK_CPP_EXPORTER` to its printed path, then run this exact test. The original
verification succeeds, but the certificate writer reports:

```text
proof expansion is unavailable for `__cpp_q_I12_FeeRateState_I7_IsEmpty`:
surface/certificate path coverage diverged at p1:
surface has 1 paths but frame certificate has 2
```

The reproduction formats the certificate immediately after verification on the
same thread. It does not run another cold verification between producing and
formatting the certificate, and does not alter the native C++ method or proof.

## Locked-header variant

The same refusal also reproduces in
`locked_header_records_preserve_declaration_sources_and_verify_offline` when
its `FeeRateState::IsEmpty` case formats the already verified whole claim.
The unchanged selected-tactic test passes. Keep the existing
`header-record/header_record.cpp` and `header-record/state.h` fixtures and
`is_empty.click` sidecar with its filename adjusted by the test; the class and
field locations must remain attributed to the locked header. This is the same
one-surface-path/two-frame-path mismatch, not a separate compiler-import error.

## Acceptance criteria

Write the complete verified `IsEmpty` claim, then independently cold-check and
retained-check the written proof with the same prepared compiler import.
Preserve the original boolean-return pattern and all three access variants;
keep the existing field-authority and false-result rejection controls.
