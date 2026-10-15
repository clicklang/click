//! Activate the first checked straight-line scalar-reference source subset.
use super::super::borrow_frontiers::{
    MirPoint, ScalarReferenceAccessKind, certify_scalar_reference_end,
};
use super::super::schema::{MirStatement as M, MirTerminator as T};
use super::*;

fn scalar_expression(expression: &E) -> bool {
    match expression {
        E::Local { .. } | E::Integer { .. } | E::UnsignedInteger { .. } | E::Boolean { .. } => true,
        E::Deref { reference, .. } => matches!(reference.as_ref(), E::Local { .. }),
        E::Binary { left, right, .. } => scalar_expression(left) && scalar_expression(right),
        E::IntegerFrom { value, .. }
        | E::Cast { value, .. }
        | E::Not { value }
        | E::BitwiseNot { value, .. } => scalar_expression(value),
        _ => false,
    }
}

pub(super) fn activate(
    function: &Function,
    identity: Option<&str>,
    body: &mut CStatement,
) -> Result<(), String> {
    let Some(identity) = identity else {
        return Ok(());
    };
    let Some(mir) = &function.mir else {
        return Ok(());
    };
    if mir.blocks.len() != 1 || !matches!(mir.blocks[0].terminator, T::Return) {
        return Ok(());
    }
    let statements = &mir.blocks[0].statements;
    let mut births =
        statements
            .iter()
            .enumerate()
            .filter_map(|(index, statement)| match statement {
                M::Assign {
                    target: E::Local { name: child },
                    value:
                        E::Borrow {
                            place,
                            value_type:
                                Type::Reference {
                                    mutable: true,
                                    pointee,
                                },
                        },
                } if matches!(
                    pointee.as_ref(),
                    Type::I32 | Type::U8 | Type::U16 | Type::U32
                ) =>
                {
                    let E::Deref { reference, .. } = place.as_ref() else {
                        return None;
                    };
                    let E::Local { name: parent } = reference.as_ref() else {
                        return None;
                    };
                    Some((index, parent, child, pointee.as_ref()))
                }
                _ => None,
            });
    let Some((borrow, parent, child, pointee)) = births.next() else {
        return Ok(());
    };
    if births.next().is_some()
        || parent == child
        || !function.parameters.iter().any(|p| p.name == *parent)
    {
        return Ok(());
    }
    let start = MirPoint {
        block: 0,
        statement: borrow,
    };
    let Ok(all) = certify_scalar_reference_end(
        function,
        identity,
        start,
        MirPoint {
            block: 0,
            statement: statements.len(),
        },
    ) else {
        return Ok(());
    };
    let Some(last) = ((borrow + 1)..statements.len()).rev().find(|index| {
        !all.memory_accesses_at(MirPoint {
            block: 0,
            statement: *index,
        })
        .is_empty()
    }) else {
        return Ok(());
    };
    if !all
        .memory_accesses_at(MirPoint {
            block: 0,
            statement: last,
        })
        .iter()
        .any(|access| {
            access.kind() == ScalarReferenceAccessKind::Write && access.reference_local() == child
        })
    {
        return Ok(());
    }
    let end = MirPoint {
        block: 0,
        statement: last + 1,
    };
    if certify_scalar_reference_end(function, identity, start, end).is_err() {
        return Ok(());
    }
    let types: BTreeMap<_, _> = function
        .parameters
        .iter()
        .chain(&mir.locals)
        .map(|p| (p.name.as_str(), &p.value_type))
        .collect();
    // Reference storage, copies and calls need the wider source protocol. The
    // memory adapter already refuses transport while an issued lease is live.
    if statements[borrow + 1..=last]
        .iter()
        .any(|statement| match statement {
            M::Assign {
                target: E::Local { name },
                value,
            } => {
                matches!(types.get(name.as_str()), Some(Type::Reference { .. }))
                    || !scalar_expression(value)
            }
            M::Assign {
                target: E::Deref { reference, .. },
                value,
            } => !matches!(reference.as_ref(), E::Local { .. }) || !scalar_expression(value),
            _ => true,
        })
    {
        return Ok(());
    }
    let matches_birth = |source: &ReferenceBorrowSourceId| {
        source.import_identity.as_ref() == identity
            && source.function.as_ref() == function.name
            && source.block == 0
            && source.statement == borrow
            && source.parent.as_ref() == parent
            && source.child.as_ref() == child
    };
    let matches_end = |source: &ReferenceAccessSourceId| {
        source.import_identity.as_ref() == identity
            && source.function.as_ref() == function.name
            && source.block == 0
            && source.statement == last
            && source.reference_local.as_ref() == child
            && source.kind == ReferenceAccessKind::Write
    };
    let mut assignment = None;
    let mut ending = None;
    let mut pending = vec![&*body];
    while let Some(statement) = pending.pop() {
        crate::instrumentation::record_deterministic_work(1);
        match statement {
            CStatement::Seq(first, second) => {
                pending.push(first);
                pending.push(second);
            }
            CStatement::Assign {
                expression, source, ..
            } if source.as_ref().is_some_and(&matches_birth) => {
                if assignment.replace(expression.clone()).is_some() {
                    return Err("ambiguous lowered scalar-reference birth".into());
                }
            }
            CStatement::TypedStore {
                pointer,
                value,
                value_type,
                volatile,
                pointee_constant,
                source,
            } if source.as_ref().is_some_and(&matches_end) => {
                let previous = ending.replace((
                    pointer.clone(),
                    value.clone(),
                    *value_type,
                    *volatile,
                    *pointee_constant,
                ));
                if previous.is_some() {
                    return Err("ambiguous lowered scalar-reference ending".into());
                }
            }
            _ => {}
        }
    }
    let plan = ScalarReferenceSourcePlan::new(
        ScalarReferencePlanKey {
            import_identity: identity.into(),
            function: function.name.as_str().into(),
            block: 0,
            borrow,
            end: end.statement,
        },
        parent.clone(),
        child.clone(),
        scalar_type(pointee)?.to_kernel_type(),
        assignment.ok_or("checked scalar-reference birth missing from lowered source plan")?,
        ending.ok_or("checked scalar-reference ending missing from lowered source plan")?,
    );
    let mut pending = vec![body];
    while let Some(statement) = pending.pop() {
        crate::instrumentation::record_deterministic_work(1);
        match statement {
            CStatement::Seq(first, second) => {
                pending.push(std::sync::Arc::make_mut(first));
                pending.push(std::sync::Arc::make_mut(second));
            }
            CStatement::Assign { source, .. } if source.as_ref().is_some_and(&matches_birth) => {
                *source = source.clone().with_lease_plan(plan.clone())
            }
            CStatement::TypedStore { source, .. } if source.as_ref().is_some_and(&matches_end) => {
                *source = source.clone().with_lease_plan(plan.clone())
            }
            _ => {}
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn source_scalar_lease_activates_unchanged_native_set_seven_witness() {
        let export = super::super::super::charon::decode(
            include_bytes!("../../../../design/charon-trial/gate-fixtures/basic/borrow.ullbc"),
            "borrow.rs",
            include_bytes!("../../../../design/charon-trial/gate-fixtures/basic/borrow.rs"),
        )
        .unwrap();
        let (functions, _) = lower_with_identity(&export, Some("native-locked-source")).unwrap();
        let helper = functions
            .iter()
            .find(|f| f.name() == "set_seven")
            .unwrap()
            .to_kernel_function();
        let mut births = 0;
        let mut endings = 0;
        let mut pending = vec![helper.body()];
        while let Some(statement) = pending.pop() {
            match statement {
                CStatement::Seq(first, second) => {
                    pending.push(first);
                    pending.push(second);
                }
                CStatement::Assign { source, .. } => {
                    births += usize::from(*source != CStatementAssignSource::default())
                }
                CStatement::TypedStore { source, .. } => {
                    endings += usize::from(*source != CStatementStoreSource::default())
                }
                _ => {}
            }
        }
        assert_eq!((births, endings), (1, 1));
    }
}
