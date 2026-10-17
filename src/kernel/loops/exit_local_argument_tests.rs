use super::*;

fn fixture(snapshot: CResourceSnapshot) -> (CLoopBinder, Vec<ResourceInstance>) {
    let schema =
        ResourceFieldSchema::new(vec![("tag".into(), ResourceFieldType::C(CType::Int32))]).unwrap();
    let spec = CResourceSpec::new(
        CResourceTerm::Instance {
            identity: Variable(99),
            binder: "c".into(),
            schema: schema.clone(),
            resource: Box::new(CResourceTerm::Composite {
                name: "cursor".into(),
                arguments: vec![c_variable("cur")],
                argument_snapshots: vec![snapshot],
                parameter_types: vec![CType::Int32],
            }),
        },
        CResourceAccessMode::Own,
        CResourceQuantity::One,
        CResourceTransferRole::Consume,
        CResourceSnapshot::Current,
    )
    .unwrap();
    let binder = CLoopBinder {
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
                vec![AlgebraicValue::C(int32(value))].into(),
                schema.clone(),
                vec![AlgebraicValue::C(int32(value))].into(),
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
        CState::new().with_local("cur", int32(1)),
        CState::new().with_local("cur", int32(2)),
    ];
    let successor = CState::new().with_local("cur", int32(3));
    for snapshot in [CResourceSnapshot::Entry, CResourceSnapshot::Post] {
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
    let (binder, instances) = fixture(CResourceSnapshot::Current);
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
        CValue::typed_pointer(
            Pointer::symbolic(Variable(880_000 + id)),
            CType::Int32Pointer,
        )
    });
    let address = |value: &CValue| {
        let CValue::Pointer(pointer) = value else {
            unreachable!()
        };
        AlgebraicValue::C(CValue::UInt64(Bitvector32Term::pointer_address(
            pointer.pointer().clone(),
        )))
    };
    let exits = [
        CState::new().with_local("cur", pointers[0].clone()),
        CState::new().with_local("cur", pointers[1].clone()),
    ];
    let successor = CState::new().with_local("cur", pointers[2].clone());
    for snapshot in [
        CResourceSnapshot::Current,
        CResourceSnapshot::Entry,
        CResourceSnapshot::Post,
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
                    vec![AlgebraicValue::C(int32(0))].into(),
                )
                .unwrap()
            })
            .collect::<Vec<_>>();
        let spec = CResourceSpec::new(
            CResourceTerm::Instance {
                identity: Variable(99),
                binder: "c".into(),
                schema,
                resource: Box::new(CResourceTerm::Composite {
                    name: "cursor".into(),
                    arguments: vec![CExpression::Cast {
                        expression: Box::new(c_variable("cur")),
                        target_type: CType::UInt64,
                        integer_mode: CIntegerCastMode::Standard,
                        pointee_struct: None,
                        pointee_volatile: false,
                        pointee_constant: false,
                        explicit_qualification: false,
                    }],
                    argument_snapshots: vec![snapshot],
                    parameter_types: vec![CType::UInt64],
                }),
            },
            CResourceAccessMode::Own,
            CResourceQuantity::One,
            CResourceTransferRole::Consume,
            CResourceSnapshot::Current,
        )
        .unwrap();
        let binder = CLoopBinder {
            identity: Variable(99),
            name: "c".into(),
            spec: Some(spec),
        };
        let contexts = [PureFactContext::new(), PureFactContext::new()];
        let expected = (snapshot == CResourceSnapshot::Current).then(|| address(&pointers[2]));
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
