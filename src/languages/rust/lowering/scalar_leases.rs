//! Emit explicit checked births and source-frontier ends while lowering each
//! selected MIR statement. The forest analysis is indexed once per function.
use super::super::borrow_frontiers::MirPoint;
use super::super::borrow_frontiers::lease_forest::{CheckedForest, certify};
use super::*;

pub(super) struct Prepared {
    forest: CheckedForest,
    pub scopes: BTreeMap<usize, std::sync::Arc<ScalarReferenceScopePlan>>,
}
pub(super) fn prepare(
    function: &Function,
    identity: Option<&str>,
    joins: Option<&[usize]>,
) -> Option<Prepared> {
    let forest = certify(function, identity, joins?)?;
    let mut scopes = BTreeMap::new();
    for (block, scope) in &forest.scopes {
        let locals = scope
            .locals
            .iter()
            .map(|(name, ty)| Some((name.clone(), scalar_type(ty).ok()?.to_kernel_type())))
            .collect::<Option<Vec<_>>>()?;
        scopes.insert(
            *block,
            ScalarReferenceScopePlan::new(scope.family.clone(), *block, scope.join, locals),
        );
    }
    Some(Prepared { forest, scopes })
}

pub(super) fn endings(prepared: &Prepared, point: MirPoint) -> CStatement {
    prepared
        .forest
        .endings
        .get(&point)
        .into_iter()
        .flatten()
        .fold(c_skip(), |prefix, key| {
            c_seq(
                prefix,
                CStatement::EndScalarReference(crate::kernel::CScalarReferenceEnd::new(
                    key.clone(),
                )),
            )
        })
}

pub(super) fn decorate(
    prepared: &Prepared,
    point: MirPoint,
    statement: &mut CStatement,
) -> Result<(), String> {
    if let Some(birth) = prepared.forest.births.get(&point) {
        let mut count = 0;
        let mut pending = vec![&mut *statement];
        while let Some(selected) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            match selected {
                CStatement::Seq(statements) => {
                    // The pair nodes beyond the first the tree held.
                    crate::instrumentation::record_deterministic_work(statements.len() - 2);
                    pending.extend(statements.iter_mut().map(std::sync::Arc::make_mut));
                }
                CStatement::Assign {
                    name,
                    expression,
                    source,
                } if name == &birth.child
                    && source.as_ref().is_some_and(|source| {
                        source.import_identity == birth.key.import_identity
                            && source.function == birth.key.function
                            && source.block == birth.key.block
                            && source.statement == point.statement
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
    let original = std::mem::replace(statement, c_skip());
    *statement = c_seq(
        original,
        endings(
            prepared,
            MirPoint {
                block: point.block,
                statement: point.statement + 1,
            },
        ),
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn source_scalar_lease_native_fixtures_use_explicit_end_operations() {
        let fixtures: &[(&[u8], &[u8], &str, usize)] = &[
            (
                include_bytes!(
                    "../../../../design/charon-trial/gate-fixtures/basic/.click/borrow/borrow.rs.ullbc"
                ),
                include_bytes!("../../../../design/charon-trial/gate-fixtures/basic/borrow.rs"),
                "set_seven",
                1,
            ),
            (
                include_bytes!(
                    "../../../../design/charon-trial/gate-fixtures/scalar-aliases/.click/borrow/borrow.rs.ullbc"
                ),
                include_bytes!(
                    "../../../../design/charon-trial/gate-fixtures/scalar-aliases/borrow.rs"
                ),
                "alias_update",
                1,
            ),
            (
                include_bytes!(
                    "../../../../design/charon-trial/gate-fixtures/scalar-read-end/.click/borrow/borrow.rs.ullbc"
                ),
                include_bytes!(
                    "../../../../design/charon-trial/gate-fixtures/scalar-read-end/borrow.rs"
                ),
                "read_before_reuse",
                1,
            ),
            (
                include_bytes!(
                    "../../../../design/charon-trial/gate-fixtures/scalar-nested-ends/.click/borrow/borrow.rs.ullbc"
                ),
                include_bytes!(
                    "../../../../design/charon-trial/gate-fixtures/scalar-nested-ends/borrow.rs"
                ),
                "shared_frontier",
                2,
            ),
            (
                include_bytes!(
                    "../../../../design/charon-trial/gate-fixtures/scalar-nested-ends/.click/borrow/borrow.rs.ullbc"
                ),
                include_bytes!(
                    "../../../../design/charon-trial/gate-fixtures/scalar-nested-ends/borrow.rs"
                ),
                "separate_frontiers",
                2,
            ),
            (
                include_bytes!(
                    "../../../../design/charon-trial/gate-fixtures/scalar-branches/.click/borrow/borrow.rs.ullbc"
                ),
                include_bytes!(
                    "../../../../design/charon-trial/gate-fixtures/scalar-branches/borrow.rs"
                ),
                "branch_update",
                1,
            ),
            (
                include_bytes!(
                    "../../../../design/charon-trial/gate-fixtures/scalar-branches/.click/borrow/borrow.rs.ullbc"
                ),
                include_bytes!(
                    "../../../../design/charon-trial/gate-fixtures/scalar-branches/borrow.rs"
                ),
                "nested_branch_update",
                2,
            ),
            (
                include_bytes!(
                    "../../../../design/charon-trial/gate-fixtures/scalar-arm-scopes/.click/borrow/borrow.rs.ullbc"
                ),
                include_bytes!(
                    "../../../../design/charon-trial/gate-fixtures/scalar-arm-scopes/borrow.rs"
                ),
                "scoped_update",
                2,
            ),
            (
                include_bytes!(
                    "../../../../design/charon-trial/gate-fixtures/scalar-arm-scopes/.click/borrow/borrow.rs.ullbc"
                ),
                include_bytes!(
                    "../../../../design/charon-trial/gate-fixtures/scalar-arm-scopes/borrow.rs"
                ),
                "nested_scopes",
                4,
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
                    CStatement::Seq(statements) => {
                        for statement in statements.iter() {
                            pending.push(statement);
                        }
                    }
                    CStatement::If {
                        then_branch,
                        else_branch,
                        ..
                    } => {
                        pending.push(then_branch);
                        pending.push(else_branch);
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
