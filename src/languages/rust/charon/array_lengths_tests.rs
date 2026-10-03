use super::*;
use crate::surface::C0VerificationSession;

const ARTIFACT: &[u8] =
    include_bytes!("../../../../design/charon-trial/array-lengths/bounds.ullbc");
const SOURCE: &[u8] = include_bytes!("../../../../design/charon-trial/array-lengths/bounds.rs");

#[test]
fn charon_scalar_slice_length_checks_declaration_and_instantiated_element() {
    for mutation in 0..5 {
        let mut artifact: TrialArtifact = serde_json::from_slice(ARTIFACT).unwrap();
        if mutation < 4 {
            let callee = artifact
                .data
                .translated
                .fun_decls
                .iter_mut()
                .find(|f| f.item_meta.lang_item == Some(LangItem::SliceLen))
                .unwrap();
            match mutation {
                0 => callee.item_meta.lang_item = None,
                1 => callee.item_meta.is_local = true,
                2 => callee.signature.is_unsafe = true,
                3 => callee.signature.inputs.clear(),
                _ => unreachable!(),
            }
        } else {
            let functions = &mut artifact.data.translated.fun_decls;
            let unsigned = functions
                .iter()
                .flat_map(|f| match &f.body {
                    a::Body::Unstructured(body) => body.body.iter().collect::<Vec<_>>(),
                    _ => vec![],
                })
                .find_map(|block| {
                    let u::TerminatorKind::Call { call, .. } = &block.terminator.kind else {
                        return None;
                    };
                    let a::FnOperand::Regular(ptr) = &call.func else {
                        return None;
                    };
                    ptr.generics
                        .types
                        .first()
                        .filter(|ty| {
                            matches!(
                                ty.kind(),
                                a::TyKind::Scalar(a::ScalarTy::Integer(a::IntegerTy::Unsigned(
                                    a::UIntTy::U32
                                )))
                            )
                        })
                        .cloned()
                })
                .unwrap();
            let mut changed = false;
            for function in functions.iter_mut() {
                let a::Body::Unstructured(body) = &mut function.body else {
                    continue;
                };
                for block in body.body.iter_mut() {
                    let u::TerminatorKind::Call { call, .. } = &mut block.terminator.kind else {
                        continue;
                    };
                    let a::FnOperand::Regular(ptr) = &mut call.func else {
                        continue;
                    };
                    if ptr.generics.types.first().is_some_and(|ty| {
                        matches!(
                            ty.kind(),
                            a::TyKind::Scalar(a::ScalarTy::Integer(a::IntegerTy::Signed(
                                a::IntTy::I32
                            )))
                        )
                    }) {
                        ptr.generics.types[0] = unsigned.clone();
                        changed = true;
                    }
                }
            }
            assert!(changed);
        }
        assert!(decode(&serde_json::to_vec(&artifact).unwrap(), "bounds.rs", SOURCE).is_err());
    }
}

#[test]
fn charon_scalar_array_length_metadata_has_bounded_shape_and_proof_work() {
    use crate::kernel::CStatement;
    fn nodes(statement: &CStatement) -> usize {
        match statement {
            CStatement::Seq(a, b) => 1 + nodes(a) + nodes(b),
            CStatement::DeclareAggregate { .. } => panic!("length must not materialize elements"),
            _ => 1,
        }
    }
    let export = decode(ARTIFACT, "bounds.rs", SOURCE).unwrap();
    let (functions, _) = super::super::lowering::lower(&export).unwrap();
    let prepared = super::super::import::prepared_for_test(export).unwrap();
    let mut samples = Vec::new();
    for (name, ty, length) in [
        ("empty_len", "uint32", 0),
        ("signed_len", "int32", 1024),
        ("million_len", "uint32", 1_000_000),
    ] {
        let _session = crate::kernel::VerificationSession::enter();
        let function = functions
            .iter()
            .find(|f| f.name() == name)
            .unwrap()
            .to_kernel_function();
        let claim = format!(
            "verifying \"bounds.rs\"; uint64 {name}(const {ty}* values) {{ ensures result == {length}u64; }} by {{ execute(); simp(); }}"
        );
        let (verified, work) = crate::instrumentation::measure_deterministic_work(|| {
            C0VerificationSession::new_program_prepared(&claim, &prepared)
        });
        verified.unwrap();
        samples.push((nodes(function.body()), work));
    }
    assert!(
        samples
            .iter()
            .all(|(shape, work)| *shape == samples[0].0 && *work <= samples[0].1 + 64),
        "{samples:?}"
    );
}
