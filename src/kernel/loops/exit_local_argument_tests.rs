use super::*;

fn fixture(snapshot: ResourceSnapshot) -> (LoopBinder, Vec<ResourceInstance>) {
    let schema = ResourceFieldSchema::new(vec![(
        "tag".into(),
        ResourceFieldType::Program(ProgramType::Int32),
    )])
    .unwrap();
    let spec = ResourceSpec::new(
        ResourceTerm::Instance {
            identity: Variable(99),
            binder: "c".into(),
            schema: schema.clone(),
            resource: Box::new(ResourceTerm::Composite {
                name: "cursor".into(),
                arguments: vec![crate::kernel::program_expression::variable("cur")],
                argument_snapshots: vec![snapshot],
                parameter_types: vec![ProgramType::Int32],
            }),
        },
        ResourceAccessMode::Own,
        ResourceQuantity::One,
        ResourceTransferRole::Consume,
        ResourceSnapshot::Current,
    )
    .unwrap();
    let binder = LoopBinder {
        identity: Variable(99),
        name: "c".into(),
        spec: Some(spec),
    };
    let instances = [1, 2]
        .into_iter()
        .map(|value| {
            ResourceInstance::new(
                Variable(99),
                "cursor".into(),
                vec![AlgebraicValue::Program(int32(value))].into(),
                schema.clone(),
                vec![AlgebraicValue::Program(int32(value))].into(),
            )
            .unwrap()
        })
        .collect();
    (binder, instances)
}

#[test]
fn exit_local_argument_requires_current_snapshot_and_every_exit() {
    let _session = crate::kernel::VerificationSession::enter();
    let exits = [
        ExecutionState::new().with_local("cur", int32(1)),
        ExecutionState::new().with_local("cur", int32(2)),
    ];
    let successor = ExecutionState::new().with_local("cur", int32(3));
    for snapshot in [ResourceSnapshot::Entry, ResourceSnapshot::Post] {
        let (binder, instances) = fixture(snapshot);
        assert_eq!(
            loop_exit_local_arguments(
                &successor,
                &exits,
                &binder,
                &instances,
                &[PureFactContext::new(), PureFactContext::new()]
            ),
            vec![None]
        );
    }
    let (binder, instances) = fixture(ResourceSnapshot::Current);
    let mismatched = [
        exits[0].clone(),
        exits[1].clone().with_local("cur", int32(4)),
    ];
    assert_eq!(
        loop_exit_local_arguments(
            &successor,
            &mismatched,
            &binder,
            &instances,
            &[PureFactContext::new(), PureFactContext::new()]
        ),
        vec![None]
    );
}

#[test]
fn exit_address_argument_tracks_only_the_declared_current_local() {
    let _session = crate::kernel::VerificationSession::enter();
    let pointers = [1, 2, 3].map(|id| {
        ProgramValue::typed_pointer(
            Pointer::symbolic(Variable(880_000 + id)),
            ProgramType::Int32Pointer,
        )
    });
    let address = |value: &ProgramValue| {
        let ProgramValue::Pointer(pointer) = value else {
            unreachable!()
        };
        AlgebraicValue::Program(ProgramValue::UInt64(MachineTerm::pointer_address(
            pointer.pointer().clone(),
        )))
    };
    let exits = [
        ExecutionState::new().with_local("cur", pointers[0].clone()),
        ExecutionState::new().with_local("cur", pointers[1].clone()),
    ];
    let successor = ExecutionState::new().with_local("cur", pointers[2].clone());
    for snapshot in [
        ResourceSnapshot::Current,
        ResourceSnapshot::Entry,
        ResourceSnapshot::Post,
    ] {
        let (_, old_instances) = fixture(snapshot);
        let schema = old_instances[0].schema.clone();
        let instances = pointers[..2]
            .iter()
            .map(|pointer| {
                ResourceInstance::new(
                    Variable(99),
                    "cursor".into(),
                    vec![address(pointer)].into(),
                    schema.clone(),
                    vec![AlgebraicValue::Program(int32(0))].into(),
                )
                .unwrap()
            })
            .collect::<Vec<_>>();
        let spec = ResourceSpec::new(
            ResourceTerm::Instance {
                identity: Variable(99),
                binder: "c".into(),
                schema,
                resource: Box::new(ResourceTerm::Composite {
                    name: "cursor".into(),
                    arguments: vec![ProgramExpression::Cast {
                        expression: Box::new(crate::kernel::program_expression::variable("cur")),
                        target_type: ProgramType::UInt64,
                        integer_mode: IntegerCastMode::Standard,
                        pointee_struct: None,
                        pointee_volatile: false,
                        pointee_constant: false,
                        explicit_qualification: false,
                    }],
                    argument_snapshots: vec![snapshot],
                    parameter_types: vec![ProgramType::UInt64],
                }),
            },
            ResourceAccessMode::Own,
            ResourceQuantity::One,
            ResourceTransferRole::Consume,
            ResourceSnapshot::Current,
        )
        .unwrap();
        let binder = LoopBinder {
            identity: Variable(99),
            name: "c".into(),
            spec: Some(spec),
        };
        let contexts = [PureFactContext::new(), PureFactContext::new()];
        let expected = (snapshot == ResourceSnapshot::Current).then(|| address(&pointers[2]));
        assert_eq!(
            loop_exit_local_arguments(&successor, &exits, &binder, &instances, &contexts),
            vec![expected]
        );
        let mismatched = [
            exits[0].clone(),
            exits[1].clone().with_local("cur", pointers[0].clone()),
        ];
        assert_eq!(
            loop_exit_local_arguments(&successor, &mismatched, &binder, &instances, &contexts),
            vec![None]
        );
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/loops/exit_local_argument_tests.rs");
}
