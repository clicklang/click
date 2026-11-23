use super::*;

fn target(name: &str, identity: u64, argument: u32) -> ResourceClause {
    ResourceClause::Named {
        binding: ResourceInstanceBinding {
            unnamed: false,
            name: name.into(),
            identity: crate::kernel::ResourceBinder::Instance(InstanceId::from_variable(Variable(
                identity,
            ))),
            children: vec![],
            schema: None,
            fields: None,
            fold_fields: None,
            child_bindings: None,
        },
        resource: Box::new(ResourceClause::Declared {
            type_schema: None,
            resource_type_arguments: vec![],
            resource_arguments: vec![],
            access: ResourceAccessMode::Own,
            kind: ResourceKind::Token,
            name: "pair".into(),
            arguments: vec![ContractExpression::ProgramExpression(
                ProgramExpression::Value(int32(argument)),
            )],
            parameter_types: vec![],
        }),
    }
}

#[test]
fn resource_selectors_are_indexed_and_restore_scoped_placeholders() {
    let mut samples = Vec::new();
    for size in [16, 64, 256, 1024] {
        let mut names = NameTable::default();
        let mut selected = target("pair(0)", 0, 0);
        let ResourceClause::Named { binding, .. } = &mut selected else {
            unreachable!()
        };
        binding.unnamed = true;
        let identity = binding.instance().unwrap();
        let call = ResourceTargets::call(&selected).unwrap();
        names.set_unnamed_instance_target(identity, selected.clone());
        for i in 1..=size {
            let name = format!("other{i}");
            names.set_instance_target(name.clone(), target(&name, i as u64, i));
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(
                names.resource_targets.select(&call).unwrap(),
                Some(&selected)
            );
            let ResourceClause::Named { resource, .. } = &selected else {
                unreachable!()
            };
            assert_eq!(names.resource_targets.hidden(resource), Some(&selected));
        });
        let scope = names.scope();
        // Many child placeholders with the same parent clause are not parents.
        for i in 1..=size {
            let name = format!("child{i}");
            names.set_child_instance_target(name.clone(), target(&name, (size + i) as u64, 0));
        }
        assert_eq!(
            names.resource_targets.select(&call).unwrap(),
            Some(&selected)
        );
        let inner = names.scope();
        names.set_unnamed_instance_target(identity, target("pair(1)", 0, 1));
        assert_eq!(names.resource_targets.select(&call).unwrap(), None);
        names.end(inner);
        assert_eq!(
            names.resource_targets.select(&call).unwrap(),
            Some(&selected)
        );
        // Related real targets make the selector ambiguous, without a scan.
        for i in 1..=size {
            let name = format!("same{i}");
            names.set_instance_target(name.clone(), target(&name, (2 * size + i) as u64, 0));
        }
        let (_, ambiguous_work) = crate::instrumentation::measure_deterministic_work(|| {
            assert!(names.resource_targets.select(&call).is_err());
        });
        names.end(scope);
        assert_eq!(
            names.resource_targets.select(&call).unwrap(),
            Some(&selected)
        );
        samples.push((work, ambiguous_work));
    }
    assert!(samples.windows(2).all(|p| p[0] == p[1]), "{samples:?}");
    assert!(samples[0].0 > 0 && samples[0].1 > 0);
}
