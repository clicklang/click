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
