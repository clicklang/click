//! Lifetime events for the supported automatic-object profile.
//!
//! Destructor identity comes from the typed local and its record, independently
//! of the artifact's exit annotations. Validation checks those annotations;
//! lowering derives exit edges from this same construction state.
use super::{CppCleanup, CppPlaceReference, CppRecord, CppStatement, CppType};
use std::collections::BTreeMap;

pub(super) struct LifetimePlan {
    destructors: BTreeMap<String, CppCleanup>,
}

impl LifetimePlan {
    pub(super) fn new<'r>(
        body: &[CppStatement],
        record_for: impl Fn(&str) -> Option<&'r CppRecord>,
    ) -> Result<Self, String> {
        let mut destructors = BTreeMap::new();
        let mut pending = vec![body];
        while let Some(body) = pending.pop() {
            for statement in body {
                crate::instrumentation::record_deterministic_work(1);
                match statement {
                    CppStatement::Declare { local, .. } => {
                        if let CppType::Record { declaration_id, .. } = &local.value_type {
                            let record = record_for(declaration_id).ok_or_else(|| {
                                format!("C++ lifetime plan found unknown record `{declaration_id}`")
                            })?;
                            if let Some(callee) = &record.destructor {
                                let cleanup = CppCleanup::Destructor {
                                    object: CppPlaceReference {
                                        projections: Vec::new(),
                                        declaration_id: local.declaration_id.clone(),
                                        name: local.name.clone(),
                                        span: local.span.clone(),
                                    },
                                    callee: callee.clone(),
                                    span: local.span.clone(),
                                };
                                if destructors
                                    .insert(local.declaration_id.clone(), cleanup)
                                    .is_some()
                                {
                                    return Err(format!(
                                        "duplicate C++ lifetime declaration `{}`",
                                        local.declaration_id
                                    ));
                                }
                            }
                        }
                    }
                    CppStatement::Scope { body, .. } => pending.push(body),
                    CppStatement::If {
                        then_branch,
                        else_branch,
                        ..
                    } => {
                        pending.push(then_branch);
                        pending.push(else_branch);
                    }
                    CppStatement::TryCatchInt32 {
                        try_body, handler, ..
                    } => {
                        pending.push(try_body);
                        pending.push(handler);
                    }
                    _ => {}
                }
            }
        }
        Ok(Self { destructors })
    }

    /// Trivial temporaries still have a lifetime. This event is derived from the
    /// resolved full expression, independently of the destructor inventory.
    pub(super) fn full_expression_temporary_type<'s>(
        &self,
        statement: &'s CppStatement,
    ) -> Option<&'s CppType> {
        match statement {
            CppStatement::AssignConstructionCall { value_type, .. } => Some(value_type),
            _ => None,
        }
    }

    /// This event occurs only on the initializer's successful continuation.
    pub(super) fn constructed<'a>(
        &'a self,
        statement: &CppStatement,
        state: &mut LifetimeState<'a>,
    ) {
        if let CppStatement::Declare { local, .. } = statement
            && matches!(local.value_type, CppType::Record { .. })
        {
            crate::instrumentation::record_deterministic_work(1);
            if let Some(cleanup) = self.destructors.get(&local.declaration_id) {
                state.live.push(cleanup);
            }
        }
    }

    pub(super) fn validate(&self, body: &[CppStatement], function: &str) -> Result<(), String> {
        self.validate_sequence(body, function, &mut LifetimeState::default())
    }

    fn validate_sequence<'a>(
        &'a self,
        body: &[CppStatement],
        function: &str,
        state: &mut LifetimeState<'a>,
    ) -> Result<(), String> {
        for statement in body {
            crate::instrumentation::record_deterministic_work(1);
            match statement {
                CppStatement::ReturnConstruct { cleanups, .. }
                | CppStatement::ReturnAggregateCall { cleanups, .. }
                | CppStatement::ReturnRecord { cleanups, .. }
                | CppStatement::Return { cleanups, .. }
                | CppStatement::ReturnCall { cleanups, .. } => {
                    if !state.matches_exit(cleanups, 0) {
                        return Err(format!(
                            "C++ return from `{function}` must destroy every constructed local exactly once in reverse construction order"
                        ));
                    }
                }
                CppStatement::Scope { body, cleanups, .. } => {
                    let mark = state.mark();
                    self.validate_sequence(body, function, state)?;
                    if !state.matches_exit(cleanups, mark) {
                        return Err(format!(
                            "nested scope in `{function}` must destroy every local exactly once in reverse construction order on fallthrough"
                        ));
                    }
                    state.restore(mark);
                }
                CppStatement::If {
                    then_branch,
                    else_branch,
                    ..
                } => {
                    let mark = state.mark();
                    self.validate_sequence(then_branch, function, state)?;
                    state.restore(mark);
                    self.validate_sequence(else_branch, function, state)?;
                    state.restore(mark);
                }
                CppStatement::TryCatchInt32 {
                    try_body, handler, ..
                } => {
                    let mark = state.mark();
                    self.validate_sequence(try_body, function, state)?;
                    state.restore(mark);
                    self.validate_sequence(handler, function, state)?;
                    state.restore(mark);
                }
                _ => {}
            }
            self.constructed(statement, state);
        }
        Ok(())
    }
}

/// Scoped construction state. Enter/leave and branch restoration retain a
/// stack cursor, rather than cloning the enclosing live-object environment.
#[derive(Default)]
pub(super) struct LifetimeState<'a> {
    live: Vec<&'a CppCleanup>,
}

impl<'a> LifetimeState<'a> {
    pub(super) fn mark(&self) -> usize {
        self.live.len()
    }
    pub(super) fn restore(&mut self, mark: usize) {
        self.live.truncate(mark);
    }
    pub(super) fn exit(
        &self,
        mark: usize,
    ) -> impl DoubleEndedIterator<Item = &'a CppCleanup> + Clone + use<'a, '_> {
        self.live[mark..].iter().rev().copied()
    }

    fn matches_exit(&self, cleanups: &[CppCleanup], mark: usize) -> bool {
        cleanups.len() == self.live.len() - mark
            && cleanups
                .iter()
                .zip(self.exit(mark))
                .all(|(actual, expected)| {
                    crate::instrumentation::record_deterministic_work(1);
                    let CppCleanup::Destructor {
                        object: a,
                        callee: ac,
                        ..
                    } = actual;
                    let CppCleanup::Destructor {
                        object: e,
                        callee: ec,
                        ..
                    } = expected;
                    a.declaration_id == e.declaration_id
                        && a.name == e.name
                        && ac.declaration_id == ec.declaration_id
                        && ac.name == ec.name
                })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::languages::cpp::{
        CppExpression, CppFunctionReference, CppInitializer, CppPlace, CppSpan,
    };

    fn span() -> CppSpan {
        CppSpan {
            file: "lifetime.cpp".into(),
            start_line: 1,
            start_column: 1,
            end_line: 1,
            end_column: 2,
        }
    }
    fn reference(name: &str) -> CppFunctionReference {
        CppFunctionReference {
            declaration_id: name.into(),
            name: name.into(),
            span: span(),
        }
    }
    fn record() -> CppRecord {
        CppRecord {
            byte_template_arguments: vec![],
            base: None,
            declaration_id: "Guard".into(),
            name: "Guard".into(),
            size_bytes: 4,
            alignment_bytes: 4,
            fields: vec![],
            destructor: Some(reference("Guard_destroy")),
            span: span(),
        }
    }
    fn declaration(name: &str) -> CppStatement {
        CppStatement::Declare {
            local: CppPlace {
                declaration_id: name.into(),
                name: name.into(),
                value_type: CppType::Record {
                    declaration_id: "Guard".into(),
                    name: "Guard".into(),
                    is_const: false,
                },
                span: span(),
            },
            initializer: CppInitializer::Constructor {
                callee: reference("Guard_construct"),
                arguments: vec![],
                span: span(),
            },
            span: span(),
        }
    }
    fn cleanup(name: &str) -> CppCleanup {
        CppCleanup::Destructor {
            object: CppPlaceReference {
                projections: Vec::new(),
                declaration_id: name.into(),
                name: name.into(),
                span: span(),
            },
            callee: reference("Guard_destroy"),
            span: span(),
        }
    }
    fn returned(cleanups: Vec<CppCleanup>) -> CppStatement {
        CppStatement::Return {
            value: CppExpression::CompilerConstant {
                value: "0".into(),
                value_type: CppType::Boolean {
                    bits: 8,
                    is_const: false,
                },
                span: span(),
            },
            cleanups,
            span: span(),
        }
    }

    #[test]
    fn exits_check_the_current_construction_prefix_and_destructor_identity() {
        let record = record();
        let body = vec![
            declaration("first"),
            returned(vec![cleanup("first")]),
            declaration("second"),
            returned(vec![cleanup("second"), cleanup("first")]),
        ];
        let plan = LifetimePlan::new(&body, |id| (id == "Guard").then_some(&record)).unwrap();
        plan.validate(&body, "caller").unwrap();
        // A later declaration must not retroactively become live on an early return.
        for bad in [
            vec![],
            vec![cleanup("second"), cleanup("first")],
            vec![cleanup("first"), cleanup("first")],
        ] {
            let mut forged = body.clone();
            forged[1] = returned(bad);
            assert!(plan.validate(&forged, "caller").is_err());
        }
        let mut forged = body.clone();
        let CppStatement::Return { cleanups, .. } = &mut forged[1] else {
            unreachable!()
        };
        let CppCleanup::Destructor { callee, .. } = &mut cleanups[0];
        callee.declaration_id = "another_destructor".into();
        assert!(plan.validate(&forged, "caller").is_err());
    }

    #[test]
    fn scoped_construction_restores_outer_state_and_never_activates_future_objects() {
        let record = record();
        let nested = vec![
            declaration("inner"),
            returned(vec![cleanup("inner"), cleanup("outer")]),
        ];
        let scope = CppStatement::Scope {
            body: nested,
            cleanups: vec![cleanup("inner")],
            span: span(),
        };
        let body = vec![
            declaration("outer"),
            scope,
            returned(vec![cleanup("outer")]),
        ];
        let plan = LifetimePlan::new(&body, |id| (id == "Guard").then_some(&record)).unwrap();
        plan.validate(&body, "caller").unwrap();
        let mut state = LifetimeState::default();
        assert_eq!(state.exit(0).count(), 0);
        plan.constructed(&body[0], &mut state);
        let mark = state.mark();
        let CppStatement::Scope { body: nested, .. } = &body[1] else {
            unreachable!()
        };
        // An exceptional initializer edge still sees only the already-live outer object.
        assert_eq!(state.exit(0).collect::<Vec<_>>(), vec![&cleanup("outer")]);
        plan.constructed(&nested[0], &mut state);
        assert_eq!(
            state.exit(mark).collect::<Vec<_>>(),
            vec![&cleanup("inner")]
        );
        state.restore(mark);
        assert_eq!(state.exit(0).collect::<Vec<_>>(), vec![&cleanup("outer")]);
    }

    #[test]
    fn lifetime_planning_and_exit_validation_scale_with_events_and_emitted_edges() {
        let record = record();
        for size in [8usize, 32, 128, 512, 1024] {
            let mut body = (0..size)
                .map(|i| declaration(&format!("guard_{i}")))
                .collect::<Vec<_>>();
            body.push(returned(
                (0..size)
                    .rev()
                    .map(|i| cleanup(&format!("guard_{i}")))
                    .collect(),
            ));
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                let plan = LifetimePlan::new(&body, |id| (id == "Guard").then_some(&record))?;
                plan.validate(&body, "caller")
            });
            result.unwrap();
            assert!(work >= size && work <= 4 * size + 4, "size {size}: {work}");
            for mutation in 0..3 {
                let mut forged = body.clone();
                let CppStatement::Return { cleanups, .. } = forged.last_mut().unwrap() else {
                    unreachable!()
                };
                match mutation {
                    0 => cleanups.swap(0, 1),
                    1 => {
                        cleanups.pop();
                    }
                    _ => {
                        cleanups[0] = cleanups[1].clone();
                    }
                }
                let plan =
                    LifetimePlan::new(&forged, |id| (id == "Guard").then_some(&record)).unwrap();
                assert!(
                    plan.validate(&forged, "caller")
                        .unwrap_err()
                        .contains("exactly once in reverse construction order")
                );
            }
        }
    }
}
