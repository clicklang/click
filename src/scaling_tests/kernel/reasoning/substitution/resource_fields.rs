use super::*;
use crate::kernel::{
    KernelFold, KernelFoldIndex, KernelIntegerOperator, KernelTermExport, KernelType,
    SharedMachineIntegerTerm, VerificationSession,
};

#[test]
fn mixed_resource_fields_substitute_without_exporting_the_integer_dag() {
    let variable = Variable(987320);
    let format = MachineIntegerType::UInt64;
    let mut work_by_size = Vec::new();
    for size in [16, 64, 256] {
        let _session = VerificationSession::enter();
        let observe = |variable| {
            let word = KernelTerm::variable(KernelType::Program(format.program_type()), variable);
            let observation = SharedMachineIntegerTerm::from_shared(format, word).unwrap();
            KernelTermImport::default().integer(&IntegerTerm::Machine(observation).into())
        };
        let operation =
            |operator, children| KernelTerm::integer_operation(operator, children).unwrap();
        let make_sum = |mut term: KernelTerm| {
            for i in 0..size {
                term = operation(
                    KernelIntegerOperator::Add,
                    vec![
                        term,
                        KernelTerm::variable(KernelType::Integer, Variable(987321 + i)),
                    ],
                );
            }
            term
        };
        let scoped = |body| {
            let call =
                KernelTerm::checked_call(KernelType::Integer, "integer_cell".into(), vec![body]);
            let zero = KernelTerm::integer_literal(0.into());
            KernelFold::new(
                KernelFoldIndex::Integer,
                Variable(987315),
                Variable(987316),
                [zero.clone(), zero.clone(), zero, call],
            )
            .unwrap()
            .into_term()
        };
        let original = scoped(make_sum(observe(variable)));
        let schema =
            ResourceFieldSchema::new(vec![("value".into(), ResourceFieldType::Integer)]).unwrap();
        let resource = Resource::Instance(
            ResourceInstance::new(
                InstanceId::from_variable(Variable(987319)),
                "mixed".into(),
                vec![].into(),
                schema,
                ResourceFieldValues::from_stored([StoredResourceField::Integer(original.clone())]),
            )
            .unwrap(),
        );
        let field = |resource| {
            let Resource::Instance(instance) = resource else {
                panic!("resource instance")
            };
            let Some(StoredResourceField::Integer(root)) = instance.fields.stored_field(0) else {
                panic!("retained Integer field")
            };
            root
        };
        let exports = KernelTermExport::integer_export_count();
        let substituted_pointer = substitute_pointer_variable_in_resource(
            &resource,
            variable,
            &Address::symbolic(Variable(987318)),
        );
        assert_eq!(field(substituted_pointer), original);
        let (substituted_word, work) = crate::instrumentation::measure_deterministic_work(|| {
            substitute_bitvector_variable_in_resource(
                &resource,
                variable,
                &MachineTerm::uint64_constant(7),
            )
        });
        assert_eq!(
            field(substituted_word),
            scoped(make_sum(KernelTerm::integer_literal(7.into())))
        );
        assert!(!original.has_cached_native_argument());
        assert_eq!(KernelTermExport::integer_export_count(), exports);
        work_by_size.push(work);
    }
    assert!(
        work_by_size.windows(2).all(|pair| pair[1] <= 5 * pair[0]),
        "{work_by_size:?}"
    );
}
