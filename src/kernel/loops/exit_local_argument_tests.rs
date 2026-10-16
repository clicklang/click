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

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/loops/exit_local_argument_tests.rs");
}
