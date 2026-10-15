// Scaling tests of `src/languages/rust/charon.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn charon_shared_iterator_lowering_and_first_read_work_are_independent_of_extent() {
    fn resize(ty: &mut Type, n: u64) {
        if let Type::Reference { pointee, .. } = ty {
            resize(pointee, n);
        }
        if let Type::Array { length, .. } = ty {
            *length = n;
        }
    }
    let mut samples = Vec::new();
    for length in [4, 1024, 1_000_000] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut export = decode(ITERATION_ARTIFACT, "iteration.rs", ITERATION_SOURCE).unwrap();
        export.functions.retain(|f| f.name == "signed");
        let f = &mut export.functions[0];
        for local in f
            .parameters
            .iter_mut()
            .chain(&mut f.mir.as_mut().unwrap().locals)
        {
            resize(&mut local.value_type, length);
        }
        let (prepared, lowering_work) = crate::instrumentation::measure_deterministic_work(|| {
            super::super::super::import::prepared_for_test(export)
        });
        let prepared = prepared.unwrap();
        let claim = format!(
            "verifying \"iteration.rs\"; fn signed(words: &[i32; {length}]) -> i32 {{ views words[0..{length}]; ensures result == old(words[0]); }} by {{ execute(); simp(); }}"
        );
        let (verified, work) = crate::instrumentation::measure_deterministic_work(|| {
            C0VerificationSession::new_program_prepared(&claim, &prepared)
        });
        verified.unwrap();
        samples.push((lowering_work, work));
    }
    assert!(
        samples
            .iter()
            .all(|(lowering, proof)| *lowering == samples[0].0 && *proof <= samples[0].1 + 128),
        "{samples:?}"
    );
}

#[test]
fn charon_owned_array_construction_and_moves_have_bounded_work_at_large_extents() {
    let mut samples = Vec::new();
    for length in [4, 1024, 1_000_000] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut export = decode(OWNED_ARRAY_ARTIFACT, "owned.rs", OWNED_ARRAY_SOURCE).unwrap();
        export.functions.retain(|f| f.name == "moved");
        export.records.retain(|r| r.name == "Packet");
        let record = &mut export.records[0];
        let old_size = record.size;
        // Grow the actual compiler-selected array field; preserve field
        // order and shift only fields lying after that region.
        let array_offset = record
            .fields
            .iter()
            .find(|f| matches!(f.value_type, Type::Array { .. }))
            .unwrap()
            .offset;
        let delta = (length - 4) * 4;
        record.size = old_size + delta;
        for field in &mut record.fields {
            if let Type::Array { length: n, .. } = &mut field.value_type {
                *n = u64::from(length);
            } else if field.offset >= array_offset + 16 {
                field.offset += delta;
            }
        }
        let mir = export.functions[0].mir.as_mut().unwrap();
        for local in &mut mir.locals {
            match &mut local.value_type {
                Type::Array { length: n, .. } => *n = u64::from(length),
                Type::Reference { pointee, .. } => {
                    if let Type::Array { length: n, .. } = pointee.as_mut() {
                        *n = u64::from(length);
                    }
                }
                _ => {}
            }
        }
        for statement in mir.blocks.iter_mut().flat_map(|b| &mut b.statements) {
            if let S::Assign {
                value: E::Repeat { length: n, .. },
                ..
            } = statement
            {
                *n = u64::from(length);
            }
            if let S::Assign {
                value:
                    E::Borrow {
                        value_type: Type::Reference { pointee, .. },
                        ..
                    },
                ..
            } = statement
                && let Type::Array { length: n, .. } = pointee.as_mut()
            {
                *n = u64::from(length);
            }
        }
        let (functions, layouts) = super::super::super::lowering::lower(&export).unwrap();
        assert_eq!(
            layouts["Packet"]
                .to_kernel_aggregate_layout()
                .fields()
                .len(),
            3
        );
        fn nodes(statement: &crate::kernel::CStatement) -> usize {
            match statement {
                crate::kernel::CStatement::Seq(a, b) => 1 + nodes(a) + nodes(b),
                _ => 1,
            }
        }
        let shape = nodes(functions[0].to_kernel_function().body());
        let prepared = super::super::super::import::prepared_for_test(export).unwrap();
        let claim = format!(
            "verifying \"owned.rs\"; fn moved(value: u32, index: usize) -> u32 {{ requires index < {length}u64; ensures result == value; }} by {{ execute(); simp(); }}"
        );
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            C0VerificationSession::new_program_prepared(&claim, &prepared)
        });
        result.unwrap();
        samples.push((shape, work));
    }
    assert!(
        samples
            .iter()
            .all(|sample| sample.0 == samples[0].0 && sample.1 <= samples[0].1 + 128),
        "{samples:?}"
    );
}

#[test]
fn charon_nonuniform_sparse_snapshots_have_bounded_work_at_large_extents() {
    let mut samples = Vec::new();
    for length in [4u32, 1024, 1_000_000] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut export = decode(
            include_bytes!("../../../../../design/charon-trial/array-snapshots/snapshots.ullbc"),
            "snapshots.rs",
            include_bytes!("../../../../../design/charon-trial/array-snapshots/snapshots.rs"),
        )
        .unwrap();
        export.functions.retain(|f| f.name == "sparse");
        let mir = export.functions[0].mir.as_mut().unwrap();
        for local in &mut mir.locals {
            match &mut local.value_type {
                Type::Array { length: n, .. } => *n = u64::from(length),
                Type::Reference { pointee, .. } => {
                    if let Type::Array { length: n, .. } = pointee.as_mut() {
                        *n = u64::from(length);
                    }
                }
                _ => {}
            }
        }
        for statement in mir.blocks.iter_mut().flat_map(|b| &mut b.statements) {
            if let S::Assign {
                value: E::Repeat { length: n, .. },
                ..
            } = statement
            {
                *n = u64::from(length);
            }
            if let S::Assign {
                value:
                    E::Borrow {
                        value_type: Type::Reference { pointee, .. },
                        ..
                    },
                ..
            } = statement
                && let Type::Array { length: n, .. } = pointee.as_mut()
            {
                *n = u64::from(length);
            }
        }
        let (functions, _) = super::super::super::lowering::lower(&export).unwrap();
        fn nodes(statement: &crate::kernel::CStatement) -> usize {
            match statement {
                crate::kernel::CStatement::Seq(a, b) => 1 + nodes(a) + nodes(b),
                _ => 1,
            }
        }
        let shape = nodes(functions[0].to_kernel_function().body());
        let prepared = super::super::super::import::prepared_for_test(export).unwrap();
        let claim = "verifying \"snapshots.rs\"; fn sparse(a: u32, b: u32) -> u32 { ensures result == b; } by { execute(); simp(); }";
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            C0VerificationSession::new_program_prepared(claim, &prepared)
        });
        result.unwrap();
        samples.push((shape, work));
    }
    assert!(
        samples
            .iter()
            .all(|sample| sample.0 == samples[0].0 && sample.1 <= samples[0].1 + 128),
        "{samples:?}"
    );
}

#[test]
fn charon_array_field_layout_and_verification_work_are_independent_of_extent() {
    let mut samples = Vec::new();
    for length in [4, 1024, 1_000_000] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut export = decode(FIELDS_ARTIFACT, "fields.rs", FIELDS_SOURCE).unwrap();
        export.functions.retain(|f| f.name == "read");
        export.records.retain(|r| r.name == "Lanes");
        for local in &mut export.functions[0].mir.as_mut().unwrap().locals {
            if let Type::Reference { pointee, .. } = &mut local.value_type
                && let Type::Array { length: n, .. } = pointee.as_mut()
            {
                *n = u64::from(length);
            }
        }
        let record = &mut export.records[0];
        record.size = length * 4 + 4;
        for field in &mut record.fields {
            if let Type::Array { length: n, .. } = &mut field.value_type {
                *n = u64::from(length);
            } else {
                field.offset = length * 4;
            }
        }
        let (_, layouts) = super::super::super::lowering::lower(&export).unwrap();
        assert_eq!(
            layouts["Lanes"].to_kernel_aggregate_layout().fields().len(),
            2
        );
        let prepared = super::super::super::import::prepared_for_test(export).unwrap();
        let sidecar = format!(
            "verifying \"fields.rs\"; fn read(state: &Lanes, index: usize) -> u32 {{ requires index == 0u64; views state.values[0..{length}]; ensures result == old(state.values[index]); }} by {{ execute(); simp(); }}"
        );
        let (verified, work) = crate::instrumentation::measure_deterministic_work(|| {
            C0VerificationSession::new_program_prepared(&sidecar, &prepared)
        });
        verified.unwrap();
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 128),
        "{samples:?}"
    );
}

#[test]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn charon_chunk_metadata_work_is_independent_of_input_length() {
    let export = decode(CHUNK_ARTIFACT, "chunks.rs", CHUNK_SOURCE).unwrap();
    let prepared = super::super::super::import::prepared_for_test(export).unwrap();
    let mut samples = Vec::new();
    for length in [0u64, 8, 1024, 1_000_000] {
        let _session = crate::kernel::VerificationSession::enter();
        let claim = format!(
            "verifying \"chunks.rs\"; fn tail(bytes: &[u8], size: usize) -> usize {{ requires bytes.len() == {length}u64; requires size == 4u64; ensures result == {}u64; }} by {{ execute(); simp(); }}",
            length % 4
        );
        let (verified, work) = crate::instrumentation::measure_deterministic_work(|| {
            C0VerificationSession::new_program_prepared(&claim, &prepared)
        });
        verified.unwrap();
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 64),
        "{samples:?}"
    );
}

#[test]
fn charon_slice_metadata_verification_work_is_independent_of_length() {
    let export = decode(SLICE_ARTIFACT, "slices.rs", SLICE_SOURCE).unwrap();
    let prepared = super::super::super::import::prepared_for_test(export).unwrap();
    let mut samples = Vec::new();
    for length in [0u64, 8, 1024, 1_000_000, u64::MAX] {
        let _session = crate::kernel::VerificationSession::enter();
        let claim = format!(
            "verifying \"slices.rs\"; fn length(bytes: &[u8]) -> usize {{ requires bytes.len() == {length}u64; ensures result == {length}u64; }} by {{ execute(); simp(); }}"
        );
        let (verified, work) = crate::instrumentation::measure_deterministic_work(|| {
            C0VerificationSession::new_program_prepared(&claim, &prepared)
        });
        verified.unwrap();
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 64),
        "{samples:?}"
    );
}

#[test]
fn charon_array_lowering_and_verification_work_do_not_expand_with_length() {
    use crate::kernel::CStatement as C;
    fn shape(s: &C) -> (usize, usize) {
        match s {
            C::Seq(a, b) => {
                let a = shape(a);
                let b = shape(b);
                (1 + a.0 + b.0, a.1 + b.1)
            }
            C::DeclareAggregate { layout, .. } => (1, layout.fields().len()),
            _ => (1, 0),
        }
    }
    let mut samples = Vec::new();
    for length in [8, 1024, 1_000_000] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut export = decode(ARRAY_ARTIFACT, "arrays.rs", ARRAY_SOURCE).unwrap();
        let mir = export
            .functions
            .iter_mut()
            .find(|f| f.name == "large_array")
            .unwrap()
            .mir
            .as_mut()
            .unwrap();
        for local in &mut mir.locals {
            if let Type::Array { length: n, .. } = &mut local.value_type {
                *n = length;
            }
        }
        for statement in mir.blocks.iter_mut().flat_map(|b| &mut b.statements) {
            match statement {
                S::Assign {
                    value: E::Repeat { length: n, .. },
                    ..
                } => *n = length,
                S::Assign {
                    value: E::UsizeInteger { value, .. },
                    ..
                } if *value == 999_999 => *value = length - 1,
                _ => {}
            }
        }
        let (functions, _) = super::super::super::lowering::lower(&export).unwrap();
        let function = functions
            .iter()
            .find(|f| f.name() == "large_array")
            .unwrap()
            .to_kernel_function();
        let shape = shape(function.body());
        assert_eq!(shape.1, 0);
        let prepared = super::super::super::import::prepared_for_test(export).unwrap();
        let (verified, work) = crate::instrumentation::measure_deterministic_work(|| {
            C0VerificationSession::new_program_prepared(
                "verifying \"arrays.rs\"; fn large_array() -> u8 { ensures result == 7; } by { execute(); simp(); }",
                &prepared,
            )
        });
        verified.unwrap();
        samples.push((length, shape, work));
    }
    eprintln!("array proof (length, nodes/fields, work): {samples:?}");
    assert!(
        samples
            .iter()
            .all(|(_, shape, work)| *shape == samples[0].1 && *work <= samples[0].2 + 64),
        "{samples:?}"
    );
}
