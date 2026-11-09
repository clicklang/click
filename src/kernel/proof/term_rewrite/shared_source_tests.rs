//! Differential checks for retained exact-rewrite sources.
use super::*;

fn imported(format: MachineIntegerType, term: &MachineTerm) -> KernelTerm {
    KernelTermImport::default()
        .machine_arithmetic(format, term)
        .unwrap()
}

#[test]
fn retained_sources_match_native_syntax_without_export() {
    let _session = VerificationSession::enter();
    use MachineIntegerType as T;
    for format in [
        T::Int8,
        T::UInt8,
        T::Int16,
        T::UInt16,
        T::Int32,
        T::UInt32,
        T::Int64,
        T::UInt64,
    ] {
        let variable = MachineTerm::Variable(Variable(992500));
        let literal = MachineTerm::Constant { format, bits: 3 };
        let sum = MachineTerm::Binary {
            format,
            op: MachineBinaryOp::Add,
            left: variable.clone().into(),
            right: literal.clone().into(),
        };
        let cast = MachineTerm::Cast {
            spelling: MachineCastSpelling::Generic,
            from: format,
            to: format,
            value: sum.clone().into(),
        };
        let conversion = MachineTerm::IntegerToMachine {
            value: IntegerTerm::Variable(Variable(992501)).into(),
            destination: format,
        };
        for source in [variable.clone(), literal.clone(), sum, cast, conversion] {
            let retained = imported(format, &source);
            let replacement = MachineTerm::Variable(Variable(992502));
            let retained_replacement = imported(format, &replacement);
            for goal in [
                source.clone(),
                MachineTerm::Binary {
                    format,
                    op: MachineBinaryOp::Add,
                    left: source.clone().into(),
                    right: source.clone().into(),
                },
                MachineTerm::Variable(Variable(992503)),
            ] {
                let mut baseline = TermRewrite::for_bits_checked(&source, &replacement);
                let expected = baseline.bits(&goal);
                let changed = baseline.changed;
                let refusal = baseline.refusal();
                let exports = KernelTermExport::machine_export_count();
                let mut rewrite = TermRewrite::for_machine_operands_checked(
                    MachineOperandView::Shared(&retained),
                    MachineOperandView::Legacy(&replacement),
                );
                assert_eq!(rewrite.bits(&goal), expected, "{format:?}, {source:?}");
                assert_eq!(rewrite.changed, changed);
                assert_eq!(rewrite.refusal(), refusal);
                assert_eq!(KernelTermExport::machine_export_count(), exports);

                let goal = IntegerTerm::Machine(
                    SharedMachineIntegerTerm::from_shared(format, imported(format, &goal)).unwrap(),
                );
                let mut baseline = TermRewrite::for_bits_checked(&source, &replacement);
                let expected = baseline.integer(&goal);
                let changed = baseline.changed;
                let refusal = baseline.refusal();
                for target in [
                    MachineOperandView::Legacy(&replacement),
                    MachineOperandView::Shared(&retained_replacement),
                ] {
                    let exports = KernelTermExport::machine_export_count();
                    let mut rewrite = TermRewrite::for_machine_operands_checked(
                        MachineOperandView::Shared(&retained),
                        target,
                    );
                    assert_eq!(rewrite.integer(&goal), expected, "{format:?}, {source:?}");
                    assert_eq!(rewrite.changed, changed);
                    assert_eq!(rewrite.refusal(), refusal);
                    assert_eq!(KernelTermExport::machine_export_count(), exports);
                }
            }
        }
    }
}

#[test]
fn retained_sources_preserve_fold_shadowing_capture_and_refusal() {
    let _session = VerificationSession::enter();
    let item = Variable(992510);
    let other = Variable(992511);
    let format = MachineIntegerType::Int32;
    let source_variable = MachineTerm::Variable(item);
    let goal = IntegerTerm::range_fold(
        IntegerRangeFoldIndex::Int32 {
            start: SharedIntegerRangeEndpoint::intern(source_variable.clone()),
            end: SharedIntegerRangeEndpoint::intern(MachineTerm::constant(10)),
        },
        IntegerTerm::constant_i64(0),
        Variable(992512),
        item,
        IntegerTerm::from_machine(
            format,
            MachineTerm::add(source_variable.clone(), MachineTerm::Variable(other)),
        )
        .unwrap(),
    );
    for (source, replacement) in [
        (source_variable.clone(), MachineTerm::Variable(other)),
        (MachineTerm::Variable(other), source_variable.clone()),
        (
            MachineTerm::add(source_variable, MachineTerm::constant(1)),
            MachineTerm::Variable(other),
        ),
    ] {
        let retained = imported(format, &source);
        let mut baseline = TermRewrite::for_bits_checked(&source, &replacement);
        let expected = baseline.integer(&goal);
        let changed = baseline.changed;
        let refusal = baseline.refusal();
        let retained_replacement = imported(format, &replacement);
        for target in [
            MachineOperandView::Legacy(&replacement),
            MachineOperandView::Shared(&retained_replacement),
        ] {
            let exports = KernelTermExport::machine_export_count();
            let mut rewrite = TermRewrite::for_machine_operands_checked(
                MachineOperandView::Shared(&retained),
                target,
            );
            assert_eq!(rewrite.integer(&goal), expected);
            assert_eq!(rewrite.changed, changed);
            assert_eq!(rewrite.refusal(), refusal);
            assert_eq!(KernelTermExport::machine_export_count(), exports);
        }
    }
}

#[test]
fn opaque_sources_and_replacements_keep_observations_and_fold_endpoints() {
    let _session = VerificationSession::enter();
    for format in [MachineIntegerType::Int32, MachineIntegerType::UInt64] {
        let x = MachineTerm::Variable(Variable(992520));
        let replacement = MachineTerm::If {
            condition: ConditionTerm::Variable(Variable(992521)).into(),
            then_term: x.clone().into(),
            else_term: MachineTerm::Variable(Variable(992522)).into(),
        };
        for (x, replacement) in [(x.clone(), replacement.clone()), (replacement, x)] {
            let sum = MachineTerm::Binary {
                format,
                op: MachineBinaryOp::Add,
                left: x.clone().into(),
                right: x.clone().into(),
            };
            // Include a whole-subexpression replacement and a missing source.
            for source in [
                x.clone(),
                sum.clone(),
                MachineTerm::Variable(Variable(992523)),
            ] {
                let expected = TermRewrite::for_bits_checked(&source, &replacement).bits(&sum);
                let root =
                    KernelTerm::retained_machine_operand(format, MachineOperandView::Legacy(&sum));
                let input = IntegerTerm::Machine(
                    SharedMachineIntegerTerm::from_shared(format, root.clone()).unwrap(),
                );
                let exports = KernelTermExport::machine_export_count();
                let mut rewrite = TermRewrite::for_bits_checked(&source, &replacement);
                let result = rewrite.integer(&input);
                assert!(rewrite.refusal().is_none());
                assert_eq!(KernelTermExport::machine_export_count(), exports);
                let IntegerTerm::Machine(value) = result else {
                    panic!("machine observation")
                };
                if source != sum {
                    assert!(value.shared_operand().is_some());
                }
                // A whole-root replacement may be the native opaque leaf itself;
                // only its enclosing arithmetic must remain shared.
                assert_eq!(value.value(), &expected);

                // Both range syntaxes retain the existing Int32 endpoint carrier.
                let endpoint = SharedIntegerRangeEndpoint::intern(x.clone())
                    .with_shared_operand(
                        root.with_machine_observation_type(MachineIntegerType::Int32),
                    )
                    .unwrap();
                let exports = KernelTermExport::machine_export_count();
                let mut rewrite = TermRewrite::for_bits_checked(&source, &replacement);
                let result = rewrite.range_endpoint(&endpoint);
                assert!(rewrite.refusal().is_none());
                assert_eq!(KernelTermExport::machine_export_count(), exports);
                assert!(result.machine_operand().shared_operand().is_some());
                assert_eq!(result.value(), &expected);
            }
        }
    }
}

#[test]
fn opaque_source_matching_preserves_existing_fold_scope_refusals() {
    let _session = VerificationSession::enter();
    let ty = MachineIntegerType::Int32;
    let item = Variable(992530);
    let other = Variable(992531);
    for binds_source in [false, true] {
        let source = MachineTerm::If {
            condition: ConditionTerm::Variable(Variable(992532)).into(),
            then_term: MachineTerm::Variable(if binds_source { item } else { other }).into(),
            else_term: MachineTerm::Variable(Variable(992533)).into(),
        };
        let to = if binds_source {
            MachineTerm::constant(7)
        } else {
            MachineTerm::Variable(item)
        };
        let native = MachineTerm::add(source.clone(), MachineTerm::Variable(item));
        let body: SharedIntegerTerm = IntegerTerm::Machine(
            SharedMachineIntegerTerm::from_shared(
                ty,
                KernelTerm::retained_machine_operand(ty, MachineOperandView::Legacy(&native)),
            )
            .unwrap(),
        )
        .into();
        let start = SharedIntegerRangeEndpoint::intern(MachineTerm::constant(0))
            .with_shared_operand(KernelTerm::retained_machine_operand(
                ty,
                MachineOperandView::Legacy(&source),
            ))
            .unwrap();
        let goal = IntegerTerm::RangeFold {
            index: IntegerRangeFoldIndex::Int32 {
                start,
                end: SharedIntegerRangeEndpoint::intern(MachineTerm::constant(10)),
            },
            initial: IntegerTerm::constant_i64(0).into(),
            accumulator: Variable(992534),
            item,
            body: body.clone(),
        };
        let exports = KernelTermExport::machine_export_count();
        let mut rewrite = TermRewrite::for_bits_checked(&source, &to);
        let _result = rewrite.integer(&goal);
        // Composite sources under C-item fold binders are deliberately
        // unsupported. Matching must not bypass that scope/capture refusal.
        assert_eq!(rewrite.refusal(), Some(RewriteRefusal::UnsupportedScope));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }
}
