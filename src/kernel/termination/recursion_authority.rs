//! Declaration authority captured before proofs, selected by recursive edge.
use super::*;

fn declaration_error(function: &str, message: impl Into<String>) -> TerminationError {
    let mut failure = error(message);
    failure.function = Some(function.to_string());
    failure
}

#[derive(Clone, Debug)]
enum DeclaredMeasure {
    Numeric {
        index: usize,
        parameter: BindingName,
    },
    Structural(usize),
    Expression {
        source: String,
        declaration: Arc<FunctionContractInterface>,
    },
}

/// The declaration inventory belongs to the program opening. It does not
/// contain descent proofs and cannot authorize a successful recursive call.
#[derive(Clone, Debug, Default)]
pub(super) struct RecursionDeclarations {
    measures: BTreeMap<String, DeclaredMeasure>,
}

#[derive(Clone, Debug)]
pub(super) struct ExpressionRecursionAuthority {
    pub source: String,
    pub declaration: Arc<FunctionContractInterface>,
}

#[derive(Clone, Debug, Default)]
pub(super) struct RecursionAuthority {
    pub refusal: Option<TerminationRefusal>,
    pub parameter_indices: BTreeMap<String, usize>,
    pub parameter: Option<BindingName>,
    pub structural_requirement: Option<usize>,
    pub structural_callees: BTreeMap<String, usize>,
    pub expression: Option<ExpressionRecursionAuthority>,
}

impl RecursionDeclarations {
    pub fn open_ordinary(
        functions: &[&ProgramFunction],
        plans: &[FunctionTerminationPlan],
    ) -> Result<Arc<Self>, TerminationError> {
        for plan in plans {
            charge_termination_work(1);
            if matches!(
                plan.recursive_measure,
                Some(
                    FunctionTerminationMeasure::NumericParameter(_)
                        | FunctionTerminationMeasure::ResourceRequirement(_)
                )
            ) {
                return Err(declaration_error(
                    &plan.function_name,
                    "legacy termination measures require independent termination inputs; ordinary contracts declare call-ranked recursion",
                ));
            }
        }
        Self::open(functions, plans)
    }

    pub fn open(
        functions: &[&ProgramFunction],
        plans: &[FunctionTerminationPlan],
    ) -> Result<Arc<Self>, TerminationError> {
        let functions = functions
            .iter()
            .map(|function| {
                charge_termination_work(1);
                (function.name(), *function)
            })
            .collect::<BTreeMap<_, _>>();
        let mut measures = BTreeMap::new();
        for plan in plans {
            charge_termination_work(1);
            let Some(function) = functions.get(plan.function_name.as_str()) else {
                continue;
            };
            let Some(measure) = &plan.recursive_measure else {
                continue;
            };
            let measure = match measure {
                FunctionTerminationMeasure::NumericParameter(index) => {
                    let parameter = function.parameters().get(*index).ok_or_else(|| {
                        declaration_error(
                            function.name(),
                            format!(
                                "termination parameter index is invalid for `{}`",
                                function.name()
                            ),
                        )
                    })?;
                    if parameter.program_type != ProgramType::Int32 {
                        return Err(declaration_error(
                            function.name(),
                            format!(
                                "termination parameter `{}` in `{}` must have type int32",
                                parameter.name,
                                function.name()
                            ),
                        ));
                    }
                    DeclaredMeasure::Numeric {
                        index: *index,
                        parameter: parameter.binding_name().clone(),
                    }
                }
                FunctionTerminationMeasure::ResourceRequirement(index) => {
                    DeclaredMeasure::Structural(*index)
                }
                FunctionTerminationMeasure::Expression(source) => {
                    let interface = function.contract_interface();
                    if !interface.has_call_ranked_recursion() {
                        return Err(declaration_error(
                            function.name(),
                            format!(
                                "the termination plan ranks `{}` by the expression measure `{source}`, but the \
                             declared `{}` carries no declared measure, so no recursive call of it owes a \
                             descent obligation",
                                function.name(),
                                function.name()
                            ),
                        ));
                    }
                    DeclaredMeasure::Expression {
                        source: source.clone(),
                        declaration: function.contract_interface.clone(),
                    }
                }
            };
            if measures
                .insert(plan.function_name.clone(), measure)
                .is_some()
            {
                return Err(error("termination plans contain a duplicate function"));
            }
        }
        // Declared expression peers are known before any body runs. Resolve
        // their measure kinds now; absent measures remain ordinary unmeasured
        // recursion obligations when the selected graph is opened.
        for (name, measure) in &measures {
            if let DeclaredMeasure::Expression { declaration, .. } = measure {
                for peer in declaration.recursion_peers() {
                    charge_termination_work(1);
                    if measures.get(peer).is_some_and(|measure| {
                        !matches!(measure, DeclaredMeasure::Expression { .. })
                    }) {
                        return Err(declaration_error(
                            name,
                            "a recursive component cannot mix an expression measure with another measure kind",
                        ));
                    }
                }
            }
        }
        Ok(Arc::new(Self { measures }))
    }

    /// Construct the selected recursion obligation from typed declarations.
    /// Graph selection can remove edges; proof-produced tactic edges can add
    /// them. Neither operation rereads a completed body's contract interface.
    pub fn select(
        &self,
        name: &str,
        callees: &BTreeSet<String>,
        allow_unused: bool,
        tactic_recursion: bool,
    ) -> Result<RecursionAuthority, TerminationError> {
        if tactic_recursion
            && matches!(
                self.measures.get(name),
                Some(DeclaredMeasure::Numeric { .. } | DeclaredMeasure::Structural(_))
            )
        {
            return Err(error(format!(
                "`{name}` recurses through a tactic application, which only an expression \
                 `decreases` measure can rank: its descent is owed at each application. \
                 Rank `{name}` by an expression over its parameters or its binders' models"
            )));
        }
        let mut authority = RecursionAuthority::default();
        if callees.is_empty() {
            if self.measures.contains_key(name) && !allow_unused {
                let mut refused = error(format!(
                    "function-level `decreases` on nonrecursive function `{name}` has no recursive edge to rank"
                ));
                refused.superfluous_recursive_measure = true;
                return Err(refused);
            }
            return Ok(authority);
        }
        if let Some(unmeasured) = std::iter::once(name)
            .chain(callees.iter().map(String::as_str))
            .inspect(|_| charge_termination_work(1))
            .find(|member| !self.measures.contains_key(*member))
        {
            authority.refusal = Some(TerminationRefusal::UnmeasuredRecursion {
                callee: if unmeasured == name {
                    callees.first().unwrap().clone()
                } else {
                    unmeasured.to_string()
                },
            });
            return Ok(authority);
        }
        match &self.measures[name] {
            DeclaredMeasure::Expression {
                source,
                declaration,
            } => {
                for callee in callees {
                    charge_termination_work(1);
                    if callee != name
                        && declaration.recursion_peers().binary_search(callee).is_err()
                    {
                        return Err(error(format!(
                            "`{name}` declares the expression `decreases` measure `{source}` and is in a \
                             recursive component with `{callee}`, but its declared interface does not name \
                             `{callee}` as a recursion peer, so a call to `{callee}` would be ranked by \
                             nothing"
                        )));
                    }
                }
                authority.expression = Some(ExpressionRecursionAuthority {
                    source: source.clone(),
                    declaration: declaration.clone(),
                });
            }
            DeclaredMeasure::Structural(index) => {
                authority.structural_requirement = Some(*index);
                for callee in callees {
                    charge_termination_work(1);
                    let DeclaredMeasure::Structural(index) = self.measures[callee] else {
                        return Err(error(
                            "a recursive component cannot mix structural and other measures",
                        ));
                    };
                    authority.structural_callees.insert(callee.clone(), index);
                }
            }
            DeclaredMeasure::Numeric { parameter, .. } => {
                authority.parameter = Some(parameter.clone());
                for member in std::iter::once(name).chain(callees.iter().map(String::as_str)) {
                    charge_termination_work(1);
                    let DeclaredMeasure::Numeric { index, .. } = self.measures[member] else {
                        return Err(error(
                            "a recursive component cannot mix numeric and structural measures",
                        ));
                    };
                    authority
                        .parameter_indices
                        .insert(member.to_string(), index);
                }
            }
        }
        Ok(authority)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn expression(name: &str, peers: &[&str]) -> ProgramFunction {
        ProgramFunction::new(ProgramType::Void, name, vec![], ProgramStatement::Skip)
            .with_recursion_measure(vec![RankingComponent::ProgramExpression(
                crate::kernel::program_expression::int32_literal(0),
            )])
            .with_recursion_peers(peers.iter().map(|peer| peer.to_string()).collect())
    }
    fn plan(name: &str, measure: FunctionTerminationMeasure) -> FunctionTerminationPlan {
        program_function_termination_plan(name, Some(measure), BTreeMap::new())
    }
    fn expression_plan(name: &str) -> FunctionTerminationPlan {
        plan(name, FunctionTerminationMeasure::Expression("0".into()))
    }
    #[test]
    fn declaration_opening_refuses_an_expression_plan_without_a_declared_measure() {
        let function = expression("f", &[]).with_recursion_measure(vec![]);
        let result = ProgramContractProof::open_ordinary(
            BTreeSet::from(["f".into()]),
            BTreeSet::new(),
            &BTreeSet::new(),
            &[&function],
            &[expression_plan("f")],
            BTreeSet::from(["f".into()]),
        );
        assert!(
            matches!(result, Err(error) if error.message.contains("carries no declared measure"))
        );
    }
    #[test]
    fn ordinary_opening_refuses_legacy_measures_before_body_execution() {
        let function = ProgramFunction::new(
            ProgramType::Void,
            "f",
            vec![ProgramParameter::new("n", ProgramType::Int32)],
            ProgramStatement::Skip,
        );
        for measure in [
            FunctionTerminationMeasure::NumericParameter(0),
            FunctionTerminationMeasure::ResourceRequirement(0),
        ] {
            let plans = [plan("f", measure)];
            assert!(RecursionDeclarations::open(&[&function], &plans).is_ok());
            let error = RecursionDeclarations::open_ordinary(&[&function], &plans).unwrap_err();
            assert!(error.message.contains("independent termination inputs"));
        }
    }

    #[test]
    fn declaration_opening_resolves_numeric_parameters_before_any_descent_proof() {
        let function = ProgramFunction::new(
            ProgramType::Void,
            "f",
            vec![crate::kernel::program_parameter("n", ProgramType::UInt32)],
            ProgramStatement::Skip,
        );
        let result = RecursionDeclarations::open(
            &[&function],
            &[plan("f", FunctionTerminationMeasure::NumericParameter(0))],
        );
        assert!(result.unwrap_err().message.contains("must have type int32"));
    }
    #[test]
    fn declared_expression_peers_must_have_compatible_measure_kinds_at_opening() {
        let f = expression("f", &["g"]);
        let g = expression("g", &[]);
        let result = RecursionDeclarations::open(
            &[&f, &g],
            &[
                expression_plan("f"),
                plan("g", FunctionTerminationMeasure::ResourceRequirement(0)),
            ],
        );
        assert!(
            result
                .unwrap_err()
                .message
                .contains("cannot mix an expression measure")
        );
    }
    #[test]
    fn selection_consumes_captured_declarations_without_reopening_the_interface() {
        let f = expression("f", &["g"]);
        let g = expression("g", &["f"]);
        let authority =
            RecursionDeclarations::open(&[&f, &g], &[expression_plan("f"), expression_plan("g")])
                .unwrap();
        // Later presentation/selection inputs cannot change the opened owner.
        let _presentation = f
            .with_recursion_measure(vec![])
            .with_recursion_peers(vec![]);
        let selected = authority
            .select("f", &BTreeSet::from(["g".into()]), false, false)
            .unwrap();
        assert_eq!(
            selected
                .expression
                .as_ref()
                .map(|authority| authority.source.as_str()),
            Some("0")
        );
        assert!(selected.refusal.is_none());
        assert!(
            authority
                .select("f", &BTreeSet::from(["other".into()]), false, false)
                .unwrap()
                .refusal
                .is_some()
        );
    }
    #[test]
    fn peer_coverage_and_component_selection_are_resolved_before_proof_execution() {
        let f = expression("f", &[]);
        let g = expression("g", &[]);
        let authority =
            RecursionDeclarations::open(&[&f, &g], &[expression_plan("f"), expression_plan("g")])
                .unwrap();
        assert!(
            authority
                .select("f", &BTreeSet::from(["g".into()]), false, false)
                .unwrap_err()
                .message
                .contains("recursion peer")
        );
        assert!(
            authority
                .select("f", &BTreeSet::new(), true, false)
                .unwrap()
                .expression
                .is_none()
        );
        assert!(
            authority
                .select("f", &BTreeSet::new(), false, false)
                .unwrap_err()
                .superfluous_recursive_measure
        );
    }
    mod scaling_tests {
        use super::*;
        include!("../../scaling_tests/kernel/termination/recursion_authority.rs");
    }
}
