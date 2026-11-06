use super::*;
use crate::kernel::{KernelTermExport, KernelTermImport, VerificationSession};

fn shared(value: &MachineTerm, format: MachineIntegerType) -> SharedMachineIntegerTerm {
    let root = KernelTermImport::default()
        .machine_arithmetic(format, value)
        .unwrap();
    let machine = SharedMachineIntegerTerm::from_shared(format, root).unwrap();
    assert!(!machine.has_boxed_operand());
    machine
}

#[test]
fn shared_machine_collectors_preserve_carriers_binders_and_loads() {
    for format in [MachineIntegerType::Int32, MachineIntegerType::UInt64] {
        let _session = VerificationSession::enter();
        let machine_variable = Variable(989961);
        let integer_variable = Variable(989962);
        let accumulator = Variable(989963);
        let item = Variable(989964);
        let folded = IntegerTerm::range_fold(
            IntegerRangeFoldIndex::Integer {
                start: IntegerTerm::constant_i64(0).into(),
                end: IntegerTerm::var(integer_variable).into(),
            },
            IntegerTerm::constant_i64(0),
            accumulator,
            item,
            IntegerTerm::Add(
                IntegerTerm::var(accumulator).into(),
                IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                    MachineIntegerType::Int32,
                    MachineTerm::Variable(accumulator),
                ))
                .into(),
            ),
        );
        let converted = MachineTerm::IntegerToMachine {
            value: folded.into(),
            destination: format,
        };
        let memory = crate::kernel::intern_c_memory(CMemory::new());
        let load = crate::kernel::eval::load_variable_for_exact_cell(
            &memory,
            &Pointer::symbolic(Variable(989965)),
            crate::kernel::LoadKind::Int32,
            4,
        );
        for leaf in [
            converted,
            crate::kernel::eval::registered_load_term_for_variable(&load).unwrap(),
        ] {
            let native = MachineTerm::Binary {
                format,
                op: MachineBinaryOp::Add,
                left: MachineTerm::Variable(machine_variable).into(),
                right: leaf.into(),
            };
            let machine = shared(&native, format);
            let observed = IntegerTerm::Machine(machine);
            let exports = KernelTermExport::machine_export_count();
            let mut expected = BTreeSet::new();
            let mut actual = BTreeSet::new();
            collect_bitvector_integer_variables(&native, &mut expected);
            collect_integer_carrier_variables(&observed, &mut actual);
            assert_eq!(actual, expected);
            actual.clear();
            collect_integer_free_variables(&observed, &mut actual);
            assert_eq!(actual, expected);
            actual.clear();
            collect_integer_bound_identities(&observed, &mut actual, &mut SeenTerms::default());
            assert_eq!(actual, expected);
            expected.clear();
            actual.clear();
            collect_bitvector_variables(&native, &mut expected);
            collect_integer_variables(&observed, &mut actual);
            assert_eq!(actual, expected);
            assert!(actual.contains(&machine_variable));
            expected.clear();
            actual.clear();
            collect_bitvector_capture_variables_seen(
                &native,
                &mut expected,
                &mut SeenTerms::default(),
            );
            collect_integer_bitvector_capture_variables(
                &observed,
                &mut actual,
                &mut SeenTerms::default(),
            );
            assert_eq!(actual, expected);
            let (mut expected_i, mut expected_c, mut actual_i, mut actual_c) = Default::default();
            collect_bitvector_binder_variables_seen(
                &native,
                &mut expected_i,
                &mut expected_c,
                &mut SeenTerms::default(),
            );
            collect_integer_binder_variables_seen(
                &observed,
                &mut actual_i,
                &mut actual_c,
                &mut SeenTerms::default(),
            );
            assert_eq!(actual_i, expected_i);
            assert_eq!(actual_c, expected_c);
            assert_eq!(
                collect_integer_scope_summary(&observed, &mut Default::default()).max,
                collect_bitvector_scope_summary(&native, &mut Default::default()).max
            );
            assert_eq!(KernelTermExport::machine_export_count(), exports);
        }
    }
}

#[test]
fn shared_fold_endpoint_collectors_keep_outer_variables_and_inner_binders() {
    let _session = VerificationSession::enter();
    let format = MachineIntegerType::Int32;
    let outer = Variable(989971);
    let item = Variable(989972);
    let accumulator = Variable(989973);
    let native = MachineTerm::Binary {
        format,
        op: MachineBinaryOp::Add,
        left: MachineTerm::Variable(outer).into(),
        right: MachineTerm::Variable(item).into(),
    };
    let machine = shared(&native, format);
    let endpoint = SharedIntegerRangeEndpoint::intern(MachineTerm::constant(0))
        .with_shared_operand(machine.shared_operand().unwrap().clone())
        .unwrap();
    let fold = IntegerTerm::range_fold(
        IntegerRangeFoldIndex::Int32 {
            start: endpoint.clone(),
            end: endpoint,
        },
        IntegerTerm::constant_i64(0),
        accumulator,
        item,
        IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
            format,
            MachineTerm::Variable(item),
        )),
    );
    let exports = KernelTermExport::machine_export_count();
    let mut variables = BTreeSet::new();
    collect_integer_variables(&fold, &mut variables);
    assert_eq!(variables, BTreeSet::from([outer, item]));
    variables.clear();
    collect_integer_bitvector_capture_variables(&fold, &mut variables, &mut SeenTerms::default());
    assert_eq!(variables, BTreeSet::from([outer, item]));
    let (mut integers, mut machines) = Default::default();
    collect_integer_binder_variables_seen(
        &fold,
        &mut integers,
        &mut machines,
        &mut SeenTerms::default(),
    );
    assert_eq!(integers, BTreeSet::from([accumulator]));
    assert_eq!(machines, BTreeSet::from([item]));
    assert_eq!(
        collect_integer_scope_summary(&fold, &mut Default::default()).max,
        accumulator.0
    );
    assert_eq!(KernelTermExport::machine_export_count(), exports);
}

#[cfg(test)]
mod scaling_tests {
    use super::*;
    include!(
        "../../../scaling_tests/kernel/reasoning/variable_collection/shared_machine_collector_tests.rs"
    );
}

#[test]
fn shared_scope_maximum_covers_empty_syntax_and_extreme_identities() {
    use crate::kernel::{KernelTerm, KernelType};
    let _session = VerificationSession::enter();
    let format = MachineIntegerType::Int32;
    let literal = shared(&MachineTerm::constant(1), format);
    assert_eq!(
        collect_machine_scope_summary(&literal, &mut Default::default()).max,
        0
    );
    let fresh = Variable::allocate_fresh().unwrap();
    let root = KernelTerm::machine_binary_shared(
        format,
        MachineBinaryOp::Add,
        [
            KernelTerm::variable(KernelType::C(CType::Int32), fresh),
            KernelTerm::variable(KernelType::C(CType::Int32), Variable(u64::MAX)),
        ],
    );
    let machine = SharedMachineIntegerTerm::from_shared(format, root).unwrap();
    assert_eq!(
        collect_machine_scope_summary(&machine, &mut Default::default()).max,
        u64::MAX
    );
}

#[test]
fn machine_fold_endpoints_retain_mathematical_variables_in_conversions() {
    for unsigned in [false, true] {
        let _session = VerificationSession::enter();
        let item = Variable(989991);
        let accumulator = Variable(989992);
        let format = if unsigned {
            MachineIntegerType::UInt64
        } else {
            MachineIntegerType::Int32
        };
        let converted = MachineTerm::IntegerToMachine {
            destination: format,
            value: IntegerTerm::var(item).into(),
        };
        let root = KernelTermImport::default()
            .machine_arithmetic(MachineIntegerType::Int32, &converted)
            .unwrap();
        let endpoint = SharedIntegerRangeEndpoint::intern(MachineTerm::constant(0))
            .with_shared_operand(root)
            .unwrap();
        let index = if unsigned {
            IntegerRangeFoldIndex::UInt64 {
                start: endpoint.clone(),
                end: endpoint,
            }
        } else {
            IntegerRangeFoldIndex::Int32 {
                start: endpoint.clone(),
                end: endpoint,
            }
        };
        let fold = IntegerTerm::range_fold(
            index,
            IntegerTerm::constant_i64(0),
            accumulator,
            item,
            IntegerTerm::var(accumulator),
        );
        let exports = KernelTermExport::machine_export_count();
        let mut variables = BTreeSet::new();
        collect_integer_free_variables(&fold, &mut variables);
        assert_eq!(
            variables,
            BTreeSet::from([item]),
            "the C item binder does not bind the Integer endpoint variable"
        );
        variables.clear();
        collect_integer_carrier_variables(&fold, &mut variables);
        assert_eq!(variables, BTreeSet::from([item, accumulator]));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }
}
