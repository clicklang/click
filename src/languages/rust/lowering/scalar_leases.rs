//! Emit explicit checked births and source-frontier ends while lowering each
//! selected MIR statement. The forest analysis is indexed once per function.
use super::super::borrow_frontiers::lease_forest::{CheckedForest, certify};
use super::*;

pub(super) fn prepare(function: &Function, identity: Option<&str>) -> Option<CheckedForest> {
    certify(function, identity)
}

pub(super) fn decorate(
    forest: &CheckedForest,
    point: usize,
    statement: &mut CStatement,
) -> Result<(), String> {
    if let Some(birth) = forest.births.get(&point) {
        let mut count = 0;
        let mut pending = vec![&mut *statement];
        while let Some(selected) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            match selected {
                CStatement::Seq(first, second) => {
                    pending.push(std::sync::Arc::make_mut(first));
                    pending.push(std::sync::Arc::make_mut(second));
                }
                CStatement::Assign {
                    name,
                    expression,
                    source,
                } if name == &birth.child
                    && source.as_ref().is_some_and(|source| {
                        source.import_identity == birth.key.import_identity
                            && source.function == birth.key.function
                            && source.block == 0
                            && source.statement == point
                            && source.parent.as_ref() == birth.parent
                            && source.child.as_ref() == birth.child
                    }) =>
                {
                    count += 1;
                    let plan = ScalarReferenceSourcePlan::new(
                        birth.key.clone(),
                        birth.parent.clone(),
                        birth.child.clone(),
                        scalar_type(&birth.pointee)?.to_kernel_type(),
                        expression.clone(),
                    );
                    *source = source.clone().with_lease_plan(plan);
                }
                _ => {}
            }
        }
        if count != 1 {
            return Err(
                "checked scalar birth does not map uniquely to its source statement".into(),
            );
        }
    }
    if let Some(endings) = forest.endings.get(&(point + 1)) {
        let original = std::mem::replace(statement, c_skip());
        let ends = endings.iter().fold(c_skip(), |prefix, key| {
            c_seq(
                prefix,
                CStatement::EndScalarReference(crate::kernel::CScalarReferenceEnd::new(
                    key.clone(),
                )),
            )
        });
        *statement = c_seq(original, ends);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn source_scalar_lease_native_fixtures_use_explicit_end_operations() {
        let fixtures: &[(&[u8], &[u8], &str, usize)] = &[
            (
                include_bytes!("../../../../design/charon-trial/gate-fixtures/basic/borrow.ullbc"),
                include_bytes!("../../../../design/charon-trial/gate-fixtures/basic/borrow.rs"),
                "set_seven",
                1,
            ),
            (
                include_bytes!(
                    "../../../../design/charon-trial/gate-fixtures/scalar-aliases/borrow.ullbc"
                ),
                include_bytes!(
                    "../../../../design/charon-trial/gate-fixtures/scalar-aliases/borrow.rs"
                ),
                "alias_update",
                1,
            ),
            (
                include_bytes!(
                    "../../../../design/charon-trial/gate-fixtures/scalar-read-end/borrow.ullbc"
                ),
                include_bytes!(
                    "../../../../design/charon-trial/gate-fixtures/scalar-read-end/borrow.rs"
                ),
                "read_before_reuse",
                1,
            ),
            (
                include_bytes!(
                    "../../../../design/charon-trial/gate-fixtures/scalar-nested-ends/borrow.ullbc"
                ),
                include_bytes!(
                    "../../../../design/charon-trial/gate-fixtures/scalar-nested-ends/borrow.rs"
                ),
                "shared_frontier",
                2,
            ),
            (
                include_bytes!(
                    "../../../../design/charon-trial/gate-fixtures/scalar-nested-ends/borrow.ullbc"
                ),
                include_bytes!(
                    "../../../../design/charon-trial/gate-fixtures/scalar-nested-ends/borrow.rs"
                ),
                "separate_frontiers",
                2,
            ),
        ];
        for &(artifact, source, function, expected) in fixtures {
            let export =
                super::super::super::charon::decode(artifact, "borrow.rs", source).unwrap();
            let (functions, _) =
                lower_with_identity(&export, Some("native-locked-source")).unwrap();
            let helper = functions
                .iter()
                .find(|f| f.name() == function)
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
                    CStatement::EndScalarReference(_) => endings += 1,
                    CStatement::TypedStore { source, .. } => {
                        assert_eq!(*source, CStatementStoreSource::default())
                    }
                    _ => {}
                }
            }
            assert_eq!((births, endings), (expected, expected), "{function}");
        }
    }
}
