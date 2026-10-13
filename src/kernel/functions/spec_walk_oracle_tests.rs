//! The spec-walk families checked against the recursive functions they
//! replaced. The originals are kept here, under `old_` names, only as an
//! oracle; they go once the walk has settled.
use super::*;

fn old_spec_proposition_is_state_independent(proposition: &SpecProposition) -> bool {
    match proposition {
        SpecProposition::Comparison { left, right, .. } => {
            old_spec_expression_is_state_independent(left)
                && old_spec_expression_is_state_independent(right)
        }
        SpecProposition::FloatClassification { expression, .. }
        | SpecProposition::Defined(expression) => {
            old_spec_expression_is_state_independent(expression)
        }
        SpecProposition::And(left, right)
        | SpecProposition::Or(left, right)
        | SpecProposition::Implies(left, right) => {
            old_spec_proposition_is_state_independent(left)
                && old_spec_proposition_is_state_independent(right)
        }
        SpecProposition::Not(body)
        | SpecProposition::ForAllMachineInteger { body, .. }
        | SpecProposition::ForAllInt32 { body, .. }
        | SpecProposition::ForAllInteger { body, .. }
        | SpecProposition::ForAllAlgebraic { body, .. }
        | SpecProposition::ForAllPointer { body, .. }
        | SpecProposition::ExistsMachineInteger { body, .. }
        | SpecProposition::ExistsInt32 { body, .. }
        | SpecProposition::ExistsInteger { body, .. }
        | SpecProposition::ExistsAlgebraic { body, .. }
        | SpecProposition::ExistsPointer { body, .. } => {
            old_spec_proposition_is_state_independent(body)
        }
        _ => false,
    }
}

fn old_spec_expression_is_state_independent(expression: &SpecExpression) -> bool {
    match expression {
        SpecExpression::Value(_) => true,
        SpecExpression::CExpression(expression) => c_expression_is_state_independent(expression),
        crate::kernel::binary_spec_expression!(left, right) => {
            old_spec_expression_is_state_independent(left)
                && old_spec_expression_is_state_independent(right)
        }
        SpecExpression::BitwiseNot(body)
        | SpecExpression::LoopEntrySnapshot(body)
        | SpecExpression::Cast(body, _) => old_spec_expression_is_state_independent(body),
        SpecExpression::If {
            condition,
            then_branch,
            else_branch,
        } => {
            old_spec_proposition_is_state_independent(condition)
                && old_spec_expression_is_state_independent(then_branch)
                && old_spec_expression_is_state_independent(else_branch)
        }
        SpecExpression::Let { value, body, .. } => {
            old_spec_expression_is_state_independent(value)
                && old_spec_expression_is_state_independent(body)
        }
        SpecExpression::PureFunctionApplication { arguments, .. } => arguments
            .iter()
            .all(old_spec_pure_function_argument_is_state_independent),
        SpecExpression::PointerOffset {
            pointer, elements, ..
        } => {
            old_spec_expression_is_state_independent(pointer)
                && old_spec_expression_is_state_independent(elements)
        }
        _ => false,
    }
}

fn old_spec_pure_function_argument_is_state_independent(
    argument: &SpecPureFunctionArgument,
) -> bool {
    match argument {
        SpecPureFunctionArgument::Value(expression) => {
            old_spec_expression_is_state_independent(expression)
        }
        SpecPureFunctionArgument::Integer(expression) => {
            old_spec_integer_expression_is_state_independent(expression)
        }
        SpecPureFunctionArgument::Algebraic(expression) => {
            old_spec_algebraic_expression_is_state_independent(expression)
        }
        SpecPureFunctionArgument::ArrayRef { .. } => false,
    }
}

fn old_spec_integer_expression_is_state_independent(expression: &SpecIntegerExpression) -> bool {
    match expression {
        SpecIntegerExpression::Term(_) => true,
        SpecIntegerExpression::FromMachine(value) => {
            old_spec_expression_is_state_independent(value)
        }
        SpecIntegerExpression::Negate(value) => {
            old_spec_integer_expression_is_state_independent(value)
        }
        crate::kernel::binary_spec_integer_expression!(left, right) => {
            old_spec_integer_expression_is_state_independent(left)
                && old_spec_integer_expression_is_state_independent(right)
        }
        SpecIntegerExpression::PureFunctionApplication { arguments, .. } => arguments
            .iter()
            .all(old_spec_pure_function_argument_is_state_independent),
        SpecIntegerExpression::ResourceField(_)
        | SpecIntegerExpression::AlgebraicMatch { .. }
        | SpecIntegerExpression::RangeFold { .. } => false,
    }
}

fn old_spec_algebraic_expression_is_state_independent(
    expression: &SpecAlgebraicExpression,
) -> bool {
    match &expression.node {
        SpecAlgebraicExpressionNode::ResourceField(_) => false,
        SpecAlgebraicExpressionNode::Variable(_) | SpecAlgebraicExpressionNode::Binding(_) => true,
        SpecAlgebraicExpressionNode::Constructor { fields, .. } => {
            fields.iter().all(|field| match field {
                SpecAlgebraicValue::C(expression) => {
                    old_spec_expression_is_state_independent(expression)
                }
                SpecAlgebraicValue::Integer(expression) => {
                    old_spec_integer_expression_is_state_independent(expression)
                }
                SpecAlgebraicValue::Algebraic(expression) => {
                    old_spec_algebraic_expression_is_state_independent(expression)
                }
            })
        }
        SpecAlgebraicExpressionNode::Match { scrutinee, arms } => {
            old_spec_algebraic_expression_is_state_independent(scrutinee)
                && arms
                    .iter()
                    .all(|arm| old_spec_algebraic_expression_is_state_independent(&arm.body))
        }
        SpecAlgebraicExpressionNode::PureFunctionApplication { arguments, .. } => arguments
            .iter()
            .all(old_spec_pure_function_argument_is_state_independent),
    }
}

fn old_spec_proposition_supports_stateful_memory_refinement(proposition: &SpecProposition) -> bool {
    match proposition {
        SpecProposition::SequenceComparison { left, right, .. } => {
            old_spec_sequence_supports_stateful_memory_refinement(left)
                && old_spec_sequence_supports_stateful_memory_refinement(right)
        }
        SpecProposition::SequenceMembership { element, sequence } => {
            old_spec_expression_supports_stateful_memory_refinement(element)
                && old_spec_sequence_supports_stateful_memory_refinement(sequence)
        }
        SpecProposition::Comparison { left, right, .. } => {
            old_spec_expression_supports_stateful_memory_refinement(left)
                && old_spec_expression_supports_stateful_memory_refinement(right)
        }
        SpecProposition::AlgebraicComparison { left, right, .. } => {
            old_spec_algebraic_expression_supports_stateful_memory_refinement(left)
                && old_spec_algebraic_expression_supports_stateful_memory_refinement(right)
        }
        SpecProposition::FloatClassification { expression, .. }
        | SpecProposition::Defined(expression) => {
            old_spec_expression_supports_stateful_memory_refinement(expression)
        }
        SpecProposition::And(left, right)
        | SpecProposition::Or(left, right)
        | SpecProposition::Implies(left, right) => {
            old_spec_proposition_supports_stateful_memory_refinement(left)
                && old_spec_proposition_supports_stateful_memory_refinement(right)
        }
        SpecProposition::Not(body)
        | SpecProposition::ForAllMachineInteger { body, .. }
        | SpecProposition::ForAllInt32 { body, .. }
        | SpecProposition::ForAllInteger { body, .. }
        | SpecProposition::ForAllAlgebraic { body, .. }
        | SpecProposition::ForAllPointer { body, .. }
        | SpecProposition::ExistsMachineInteger { body, .. }
        | SpecProposition::ExistsInt32 { body, .. }
        | SpecProposition::ExistsInteger { body, .. }
        | SpecProposition::ExistsAlgebraic { body, .. }
        | SpecProposition::ExistsPointer { body, .. } => {
            old_spec_proposition_supports_stateful_memory_refinement(body)
        }
        SpecProposition::IntegerComparison { .. }
        | SpecProposition::Predicate { .. }
        | SpecProposition::ResourceSeparate { .. }
        | SpecProposition::ResourceContains { .. }
        | SpecProposition::MemoryLoadable { .. } => false,
    }
}

fn old_spec_sequence_supports_stateful_memory_refinement(
    sequence: &SpecSequenceExpression,
) -> bool {
    match sequence {
        SpecSequenceExpression::Literal(elements) => elements
            .iter()
            .all(old_spec_expression_supports_stateful_memory_refinement),
        SpecSequenceExpression::Concat(left, right) => {
            old_spec_sequence_supports_stateful_memory_refinement(left)
                && old_spec_sequence_supports_stateful_memory_refinement(right)
        }
    }
}

fn old_spec_expression_supports_stateful_memory_refinement(expression: &SpecExpression) -> bool {
    match expression {
        // A field read names an instance the two interfaces share. Both the
        // current and the entry projection lower through
        // `resource_instance_at_path` against the state the caller supplies;
        // a projection the state cannot answer refuses the refinement there.
        SpecExpression::ResourceField { .. } => true,
        SpecExpression::Value(_) => true,
        SpecExpression::IntegerToMachine { .. } => false,
        SpecExpression::CExpression(expression) => {
            c_expression_supports_stateful_memory_refinement(expression)
        }
        crate::kernel::binary_spec_expression!(left, right) => {
            old_spec_expression_supports_stateful_memory_refinement(left)
                && old_spec_expression_supports_stateful_memory_refinement(right)
        }
        SpecExpression::BitwiseNot(body) | SpecExpression::Cast(body, _) => {
            old_spec_expression_supports_stateful_memory_refinement(body)
        }
        SpecExpression::If {
            condition,
            then_branch,
            else_branch,
        } => {
            old_spec_proposition_supports_stateful_memory_refinement(condition)
                && old_spec_expression_supports_stateful_memory_refinement(then_branch)
                && old_spec_expression_supports_stateful_memory_refinement(else_branch)
        }
        SpecExpression::Let { value, body, .. } => {
            old_spec_expression_supports_stateful_memory_refinement(value)
                && old_spec_expression_supports_stateful_memory_refinement(body)
        }
        SpecExpression::PureFunctionApplication { arguments, .. } => arguments
            .iter()
            .all(old_spec_pure_function_argument_supports_stateful_memory_refinement),
        SpecExpression::PointerOffset {
            pointer, elements, ..
        } => {
            old_spec_expression_supports_stateful_memory_refinement(pointer)
                && old_spec_expression_supports_stateful_memory_refinement(elements)
        }
        SpecExpression::MemoryLoad {
            memory: SpecMemory::Current | SpecMemory::FunctionEntry,
            pointer,
            ..
        } => old_spec_expression_supports_stateful_memory_refinement(pointer),
        SpecExpression::AlgebraicMatch { scrutinee, arms } => {
            old_spec_algebraic_expression_supports_stateful_memory_refinement(scrutinee)
                && arms
                    .iter()
                    .all(|arm| old_spec_expression_supports_stateful_memory_refinement(&arm.body))
        }
        SpecExpression::CountedResourceCount { .. }
        | SpecExpression::RangeFold { .. }
        | SpecExpression::LoopEntrySnapshot(_)
        | SpecExpression::MemoryLoad { .. }
        | SpecExpression::AggregateFieldValue { .. } => false,
    }
}

fn old_spec_algebraic_expression_supports_stateful_memory_refinement(
    expression: &SpecAlgebraicExpression,
) -> bool {
    match &expression.node {
        SpecAlgebraicExpressionNode::Variable(_)
        | SpecAlgebraicExpressionNode::Binding(_)
        | SpecAlgebraicExpressionNode::ResourceField(_) => true,
        SpecAlgebraicExpressionNode::Constructor { fields, .. } => fields
            .iter()
            .all(old_spec_algebraic_value_supports_stateful_memory_refinement),
        SpecAlgebraicExpressionNode::Match { scrutinee, arms } => {
            old_spec_algebraic_expression_supports_stateful_memory_refinement(scrutinee)
                && arms.iter().all(|arm| {
                    old_spec_algebraic_expression_supports_stateful_memory_refinement(&arm.body)
                })
        }
        SpecAlgebraicExpressionNode::PureFunctionApplication { arguments, .. } => arguments
            .iter()
            .all(old_spec_pure_function_argument_supports_stateful_memory_refinement),
    }
}

fn old_spec_algebraic_value_supports_stateful_memory_refinement(
    value: &SpecAlgebraicValue,
) -> bool {
    match value {
        SpecAlgebraicValue::C(expression) => {
            old_spec_expression_supports_stateful_memory_refinement(expression)
        }
        // Mathematical `Integer` values keep the exclusion that
        // `SpecPureFunctionArgument::Integer` already states.
        SpecAlgebraicValue::Integer(_) => false,
        SpecAlgebraicValue::Algebraic(expression) => {
            old_spec_algebraic_expression_supports_stateful_memory_refinement(expression)
        }
    }
}

fn old_spec_pure_function_argument_supports_stateful_memory_refinement(
    argument: &SpecPureFunctionArgument,
) -> bool {
    match argument {
        SpecPureFunctionArgument::Value(expression) => {
            old_spec_expression_supports_stateful_memory_refinement(expression)
        }
        SpecPureFunctionArgument::Integer(_) => false,
        SpecPureFunctionArgument::Algebraic(expression) => {
            old_spec_algebraic_expression_supports_stateful_memory_refinement(expression)
        }
        // An array snapshot is an explicit memory image; its stateful
        // refinement law is not written down.
        SpecPureFunctionArgument::ArrayRef { .. } => false,
    }
}

fn old_spec_algebraic_expression_is_obligation_free(expression: &SpecAlgebraicExpression) -> bool {
    match &expression.node {
        SpecAlgebraicExpressionNode::Variable(_) | SpecAlgebraicExpressionNode::Binding(_) => true,
        SpecAlgebraicExpressionNode::Constructor { fields, .. } => {
            fields.iter().all(|field| match field {
                SpecAlgebraicValue::C(value) => old_spec_value_is_obligation_free(value),
                SpecAlgebraicValue::Integer(value) => old_spec_integer_is_obligation_free(value),
                SpecAlgebraicValue::Algebraic(value) => {
                    old_spec_algebraic_expression_is_obligation_free(value)
                }
            })
        }
        SpecAlgebraicExpressionNode::PureFunctionApplication { name, arguments } => {
            name != "to_nat" && arguments.iter().all(old_spec_argument_is_obligation_free)
        }
        SpecAlgebraicExpressionNode::Match { scrutinee, arms } => {
            if !old_spec_algebraic_expression_is_obligation_free(scrutinee)
                || arms.len() != scrutinee.algebraic_type.variants.len()
            {
                return false;
            }
            let variants = scrutinee
                .algebraic_type
                .variants
                .iter()
                .map(|variant| (variant.name.as_str(), variant.fields.len()))
                .collect::<BTreeMap<_, _>>();
            let mut seen = BTreeSet::new();
            arms.iter().all(|arm| {
                seen.insert(arm.variant.as_str())
                    && variants.get(arm.variant.as_str()) == Some(&arm.bindings.len())
                    && old_spec_algebraic_expression_is_obligation_free(&arm.body)
            })
        }
        SpecAlgebraicExpressionNode::ResourceField(_) => false,
    }
}

fn old_spec_argument_is_obligation_free(argument: &SpecPureFunctionArgument) -> bool {
    match argument {
        SpecPureFunctionArgument::Value(value) => old_spec_value_is_obligation_free(value),
        SpecPureFunctionArgument::Integer(value) => old_spec_integer_is_obligation_free(value),
        SpecPureFunctionArgument::Algebraic(value) => {
            old_spec_algebraic_expression_is_obligation_free(value)
        }
        SpecPureFunctionArgument::ArrayRef { .. } => false,
    }
}

fn old_spec_value_is_obligation_free(value: &SpecExpression) -> bool {
    matches!(
        value,
        SpecExpression::Value(_)
            | SpecExpression::CExpression(
                CExpression::Value(_) | CExpression::Variable(_) | CExpression::FunctionAddress(_)
            )
    )
}

fn old_spec_integer_is_obligation_free(value: &SpecIntegerExpression) -> bool {
    match value {
        SpecIntegerExpression::Term(_) => true,
        SpecIntegerExpression::Negate(inner) => old_spec_integer_is_obligation_free(inner),
        SpecIntegerExpression::Add(left, right)
        | SpecIntegerExpression::Subtract(left, right)
        | SpecIntegerExpression::Multiply(left, right) => {
            old_spec_integer_is_obligation_free(left) && old_spec_integer_is_obligation_free(right)
        }
        SpecIntegerExpression::TruncatingQuotient(_, _)
        | SpecIntegerExpression::TruncatingRemainder(_, _) => false,
        SpecIntegerExpression::PureFunctionApplication { arguments, .. } => {
            arguments.iter().all(old_spec_argument_is_obligation_free)
        }
        SpecIntegerExpression::AlgebraicMatch { .. } => false,
        SpecIntegerExpression::FromMachine(_) | SpecIntegerExpression::ResourceField(_) => false,
        SpecIntegerExpression::RangeFold { .. } => false,
    }
}

fn old_observes_resource_state(proposition: &SpecProposition) -> bool {
    enum Node<'a> {
        Proposition(&'a SpecProposition),
        Expression(&'a SpecExpression),
        Integer(&'a SpecIntegerExpression),
        Algebraic(&'a SpecAlgebraicExpression),
        Sequence(&'a SpecSequenceExpression),
        Argument(&'a SpecPureFunctionArgument),
    }
    let mut pending = vec![Node::Proposition(proposition)];
    while let Some(node) = pending.pop() {
        if crate::instrumentation::deadline_exceeded_with_work(1) {
            // An incomplete walk cannot certify independence from the model.
            return true;
        }
        match node {
            Node::Proposition(proposition) => match proposition {
                SpecProposition::Comparison { left, right, .. } => {
                    pending.extend([Node::Expression(left), Node::Expression(right)]);
                }
                SpecProposition::IntegerComparison { left, right, .. } => {
                    pending.extend([Node::Integer(left), Node::Integer(right)]);
                }
                SpecProposition::AlgebraicComparison { left, right, .. } => {
                    pending.extend([Node::Algebraic(left), Node::Algebraic(right)]);
                }
                SpecProposition::SequenceComparison { left, right, .. } => {
                    pending.extend([Node::Sequence(left), Node::Sequence(right)]);
                }
                SpecProposition::SequenceMembership { element, sequence } => {
                    pending.extend([Node::Expression(element), Node::Sequence(sequence)]);
                }
                SpecProposition::Defined(expression)
                | SpecProposition::FloatClassification { expression, .. } => {
                    pending.push(Node::Expression(expression));
                }
                SpecProposition::And(left, right)
                | SpecProposition::Or(left, right)
                | SpecProposition::Implies(left, right) => {
                    pending.extend([Node::Proposition(left), Node::Proposition(right)]);
                }
                SpecProposition::Not(body)
                | SpecProposition::ForAllMachineInteger { body, .. }
                | SpecProposition::ForAllInt32 { body, .. }
                | SpecProposition::ForAllInteger { body, .. }
                | SpecProposition::ForAllAlgebraic { body, .. }
                | SpecProposition::ForAllPointer { body, .. }
                | SpecProposition::ExistsMachineInteger { body, .. }
                | SpecProposition::ExistsInt32 { body, .. }
                | SpecProposition::ExistsInteger { body, .. }
                | SpecProposition::ExistsAlgebraic { body, .. }
                | SpecProposition::ExistsPointer { body, .. } => {
                    pending.push(Node::Proposition(body));
                }
                SpecProposition::Predicate {
                    resource_state_dependent,
                    arguments,
                    ..
                } => {
                    if *resource_state_dependent {
                        return true;
                    }
                    for argument in arguments {
                        pending.push(Node::Expression(match argument {
                            SpecPredicateArgument::Value(expression)
                            | SpecPredicateArgument::ArrayRef {
                                pointer: expression,
                                ..
                            } => expression,
                        }));
                    }
                }
                SpecProposition::MemoryLoadable {
                    base, start, end, ..
                } => {
                    pending.extend([
                        Node::Expression(base),
                        Node::Expression(start),
                        Node::Expression(end),
                    ]);
                }
                SpecProposition::ResourceSeparate { .. }
                | SpecProposition::ResourceContains { .. } => return true,
            },
            Node::Expression(expression) => match expression {
                SpecExpression::CountedResourceCount { .. }
                | SpecExpression::ResourceField { .. } => return true,
                SpecExpression::PureFunctionApplication { arguments, .. } => {
                    pending.extend(arguments.iter().map(Node::Argument));
                }
                SpecExpression::Value(_) | SpecExpression::CExpression(_) => {}
                SpecExpression::IntegerToMachine { value, .. } => {
                    pending.push(Node::Integer(value))
                }
                crate::kernel::binary_spec_expression!(left, right) => {
                    pending.extend([Node::Expression(left), Node::Expression(right)]);
                }
                SpecExpression::BitwiseNot(inner)
                | SpecExpression::Cast(inner, _)
                | SpecExpression::LoopEntrySnapshot(inner) => pending.push(Node::Expression(inner)),
                SpecExpression::MemoryLoad { pointer, .. }
                | SpecExpression::AggregateFieldValue { pointer, .. } => {
                    pending.push(Node::Expression(pointer))
                }
                SpecExpression::PointerOffset {
                    pointer, elements, ..
                } => {
                    pending.extend([Node::Expression(pointer), Node::Expression(elements)]);
                }
                SpecExpression::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    pending.extend([
                        Node::Proposition(condition),
                        Node::Expression(then_branch),
                        Node::Expression(else_branch),
                    ]);
                }
                SpecExpression::Let { value, body, .. } => {
                    pending.extend([Node::Expression(value), Node::Expression(body)]);
                }
                SpecExpression::RangeFold {
                    start,
                    end,
                    initial,
                    body,
                    ..
                } => {
                    pending.extend([
                        Node::Expression(start),
                        Node::Expression(end),
                        Node::Expression(initial),
                        Node::Expression(body),
                    ]);
                }
                SpecExpression::AlgebraicMatch { scrutinee, arms } => {
                    pending.push(Node::Algebraic(scrutinee));
                    pending.extend(arms.iter().map(|arm| Node::Expression(&arm.body)));
                }
            },
            Node::Integer(integer) => match integer {
                SpecIntegerExpression::ResourceField(_) => return true,
                SpecIntegerExpression::PureFunctionApplication { arguments, .. } => {
                    pending.extend(arguments.iter().map(Node::Argument));
                }
                SpecIntegerExpression::Term(_) => {}
                SpecIntegerExpression::FromMachine(expression) => {
                    pending.push(Node::Expression(expression))
                }
                SpecIntegerExpression::Negate(inner) => pending.push(Node::Integer(inner)),
                crate::kernel::binary_spec_integer_expression!(left, right) => {
                    pending.extend([Node::Integer(left), Node::Integer(right)]);
                }
                SpecIntegerExpression::AlgebraicMatch { scrutinee, arms } => {
                    pending.push(Node::Algebraic(scrutinee));
                    pending.extend(arms.iter().map(|arm| Node::Integer(&arm.body)));
                }
                SpecIntegerExpression::RangeFold {
                    index,
                    initial,
                    body,
                    ..
                } => {
                    pending.extend([Node::Integer(initial), Node::Integer(body)]);
                    match index {
                        SpecIntegerRangeFoldIndex::Int32 { start, end }
                        | SpecIntegerRangeFoldIndex::UInt64 { start, end } => {
                            pending.extend([Node::Expression(start), Node::Expression(end)]);
                        }
                        SpecIntegerRangeFoldIndex::Integer { start, end } => {
                            pending.extend([Node::Integer(start), Node::Integer(end)]);
                        }
                    }
                }
            },
            Node::Argument(argument) => pending.push(match argument {
                SpecPureFunctionArgument::Value(expression)
                | SpecPureFunctionArgument::ArrayRef {
                    pointer: expression,
                    ..
                } => Node::Expression(expression),
                SpecPureFunctionArgument::Integer(integer) => Node::Integer(integer),
                SpecPureFunctionArgument::Algebraic(algebraic) => Node::Algebraic(algebraic),
            }),
            Node::Sequence(sequence) => match sequence {
                SpecSequenceExpression::Literal(elements) => {
                    pending.extend(elements.iter().map(Node::Expression));
                }
                SpecSequenceExpression::Concat(left, right) => {
                    pending.extend([Node::Sequence(left), Node::Sequence(right)]);
                }
            },
            Node::Algebraic(algebraic) => match &algebraic.node {
                SpecAlgebraicExpressionNode::Variable(_)
                | SpecAlgebraicExpressionNode::Binding(_) => {}
                SpecAlgebraicExpressionNode::ResourceField(_) => return true,
                SpecAlgebraicExpressionNode::PureFunctionApplication { arguments, .. } => {
                    pending.extend(arguments.iter().map(Node::Argument));
                }
                SpecAlgebraicExpressionNode::Constructor { fields, .. } => {
                    for field in fields {
                        pending.push(match field {
                            SpecAlgebraicValue::C(expression) => Node::Expression(expression),
                            SpecAlgebraicValue::Integer(integer) => Node::Integer(integer),
                            SpecAlgebraicValue::Algebraic(algebraic) => Node::Algebraic(algebraic),
                        });
                    }
                }
                SpecAlgebraicExpressionNode::Match { scrutinee, arms } => {
                    pending.push(Node::Algebraic(scrutinee));
                    pending.extend(arms.iter().map(|arm| Node::Algebraic(&arm.body)));
                }
            },
        }
    }
    false
}

/// Small deterministic generator of mixed spec trees.
struct Gen(u64);

impl Gen {
    fn pick(&mut self, n: u64) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0 % n
    }

    fn ty(&self) -> AlgebraicType {
        let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![
            AlgebraicVariantType {
                name: "One".into(),
                fields: vec![AlgebraicValueType::Integer],
            },
            AlgebraicVariantType {
                name: "Two".into(),
                fields: vec![],
            },
        ]
        .into();
        AlgebraicType {
            rigid: false,
            name: "Choice".into(),
            arguments: vec![],
            variants: variants.clone(),
            schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
                AlgebraicValueType::Algebraic {
                    name: "Choice".into(),
                    arguments: vec![],
                },
                variants,
            )]))),
        }
    }

    fn memory(&mut self) -> SpecMemory {
        match self.pick(4) {
            0 => SpecMemory::Current,
            1 => SpecMemory::FunctionEntry,
            2 => SpecMemory::LoopEntry,
            _ => SpecMemory::Fixed(CMemory::new()),
        }
    }

    fn c(&mut self) -> CExpression {
        match self.pick(3) {
            0 => CExpression::Variable("x".into()),
            1 => CExpression::Value(CValue::Int32(Bitvector32Term::Constant(1))),
            _ => CExpression::Load(Box::new(CExpression::Variable("p".into()))),
        }
    }

    /// A load address: often a constant offset from the parameter `x`.
    fn pointer(&mut self, depth: u32) -> SpecExpression {
        let parameter = SpecExpression::CExpression(CExpression::Variable("x".into()));
        match self.pick(3) {
            0 => parameter,
            1 => SpecExpression::PointerOffset {
                pointer: Box::new(parameter),
                elements: Box::new(SpecExpression::Value(CValue::Int32(
                    Bitvector32Term::Constant(2),
                ))),
                byte_width: 4,
            },
            _ => self.expr(depth),
        }
    }

    fn expr(&mut self, depth: u32) -> SpecExpression {
        let leaf = SpecExpression::Value(CValue::Int32(Bitvector32Term::Constant(7)));
        if depth == 0 {
            return match self.pick(2) {
                0 => leaf,
                _ => SpecExpression::CExpression(self.c()),
            };
        }
        let d = depth - 1;
        match self.pick(19) {
            0 => leaf,
            1 => SpecExpression::CExpression(self.c()),
            2 => SpecExpression::IntegerToMachine {
                value: Box::new(self.int(d)),
                destination: MachineIntegerType::Int32,
            },
            3 => SpecExpression::Add(Box::new(self.expr(d)), Box::new(self.expr(d))),
            4 => SpecExpression::BitwiseNot(Box::new(self.expr(d))),
            5 => SpecExpression::Cast(Box::new(self.expr(d)), CType::Int32),
            6 => SpecExpression::LoopEntrySnapshot(Box::new(self.expr(d))),
            7 => SpecExpression::If {
                condition: Box::new(self.prop(d)),
                then_branch: Box::new(self.expr(d)),
                else_branch: Box::new(self.expr(d)),
            },
            8 => SpecExpression::RangeFold {
                start: Box::new(self.expr(d)),
                end: Box::new(self.expr(d)),
                initial: Box::new(self.expr(d)),
                accumulator: "acc".into(),
                item: "i".into(),
                body: Box::new(self.expr(d)),
            },
            9 => SpecExpression::Let {
                name: "v".into(),
                value: Box::new(self.expr(d)),
                body: Box::new(self.expr(d)),
            },
            10 => SpecExpression::PureFunctionApplication {
                name: "f".into(),
                arguments: vec![self.arg(d), self.arg(d)],
                result_type: CType::Int32,
            },
            11 => SpecExpression::PointerOffset {
                pointer: Box::new(self.expr(d)),
                elements: Box::new(self.expr(d)),
                byte_width: 4,
            },
            12 => SpecExpression::MemoryLoad {
                memory: self.memory(),
                pointer: Box::new(self.pointer(d)),
                value_type: CType::Int32,
            },
            13 => SpecExpression::AggregateFieldValue {
                parameter: "s".into(),
                pointer: Box::new(self.pointer(d)),
                value_type: CType::Int32,
            },
            14 => SpecExpression::CountedResourceCount {
                name: "member".into(),
                arguments: vec![Some(self.expr(d)), None],
            },
            15 => SpecExpression::AlgebraicMatch {
                scrutinee: Box::new(self.alg(d)),
                arms: vec![SpecAlgebraicMatchArm {
                    variant: "Two".into(),
                    bindings: vec![],
                    binding_types: vec![],
                    body: self.expr(d),
                }],
            },
            16 => SpecExpression::Multiply(Box::new(self.expr(d)), Box::new(self.expr(d))),
            17 => SpecExpression::ShiftRight(Box::new(self.expr(d)), Box::new(self.expr(d))),
            _ => SpecExpression::BitwiseXor(Box::new(self.expr(d)), Box::new(self.expr(d))),
        }
    }

    fn int(&mut self, depth: u32) -> SpecIntegerExpression {
        let leaf = SpecIntegerExpression::Term(IntegerTerm::constant_i64(3));
        if depth == 0 {
            return leaf;
        }
        let d = depth - 1;
        match self.pick(10) {
            0 => leaf,
            1 => SpecIntegerExpression::FromMachine(Box::new(self.expr(d))),
            2 => SpecIntegerExpression::Negate(Box::new(self.int(d))),
            3 => SpecIntegerExpression::Add(Box::new(self.int(d)), Box::new(self.int(d))),
            4 => SpecIntegerExpression::TruncatingQuotient(
                Box::new(self.int(d)),
                Box::new(self.int(d)),
            ),
            5 => SpecIntegerExpression::PureFunctionApplication {
                name: "g".into(),
                arguments: vec![self.arg(d)],
            },
            6 => SpecIntegerExpression::RangeFold {
                index: match self.pick(2) {
                    0 => SpecIntegerRangeFoldIndex::Int32 {
                        start: Box::new(self.expr(d)),
                        end: Box::new(self.expr(d)),
                    },
                    _ => SpecIntegerRangeFoldIndex::Integer {
                        start: Box::new(self.int(d)),
                        end: Box::new(self.int(d)),
                    },
                },
                initial: Box::new(self.int(d)),
                accumulator: Variable(900_001),
                item: Variable(900_002),
                body: Box::new(self.int(d)),
            },
            7 => SpecIntegerExpression::Multiply(Box::new(self.int(d)), Box::new(self.int(d))),
            8 => SpecIntegerExpression::Subtract(Box::new(self.int(d)), Box::new(self.int(d))),
            _ => SpecIntegerExpression::TruncatingRemainder(
                Box::new(self.int(d)),
                Box::new(self.int(d)),
            ),
        }
    }

    fn alg(&mut self, depth: u32) -> SpecAlgebraicExpression {
        let algebraic_type = self.ty();
        let node = if depth == 0 {
            match self.pick(2) {
                0 => SpecAlgebraicExpressionNode::Variable(Variable(900_010)),
                _ => SpecAlgebraicExpressionNode::Binding("b".into()),
            }
        } else {
            let d = depth - 1;
            match self.pick(6) {
                0 => SpecAlgebraicExpressionNode::Variable(Variable(900_010)),
                1 => SpecAlgebraicExpressionNode::Constructor {
                    variant: "One".into(),
                    fields: vec![match self.pick(3) {
                        0 => SpecAlgebraicValue::C(self.expr(d)),
                        1 => SpecAlgebraicValue::Integer(self.int(d)),
                        _ => SpecAlgebraicValue::Algebraic(self.alg(d)),
                    }],
                },
                2 | 3 => {
                    let full = self.pick(2) == 0;
                    let mut arms = vec![SpecAlgebraicResultMatchArm {
                        variant: "Two".into(),
                        bindings: vec![],
                        binding_types: vec![],
                        binding_variables: vec![],
                        body: Box::new(self.alg(d)),
                    }];
                    if full {
                        arms.push(SpecAlgebraicResultMatchArm {
                            variant: "One".into(),
                            bindings: vec!["n".into()],
                            binding_types: vec![AlgebraicValueType::Integer],
                            binding_variables: vec![Some(Variable(900_011))],
                            body: Box::new(self.alg(d)),
                        });
                    }
                    SpecAlgebraicExpressionNode::Match {
                        scrutinee: Box::new(self.alg(d)),
                        arms,
                    }
                }
                4 => SpecAlgebraicExpressionNode::PureFunctionApplication {
                    name: if self.pick(3) == 0 {
                        "to_nat".into()
                    } else {
                        "h".into()
                    },
                    arguments: vec![self.arg(d)],
                },
                _ => SpecAlgebraicExpressionNode::Binding("b".into()),
            }
        };
        SpecAlgebraicExpression {
            algebraic_type,
            node,
        }
    }

    fn arg(&mut self, depth: u32) -> SpecPureFunctionArgument {
        match self.pick(4) {
            0 => SpecPureFunctionArgument::Value(self.expr(depth)),
            1 => SpecPureFunctionArgument::Integer(self.int(depth)),
            2 => SpecPureFunctionArgument::Algebraic(self.alg(depth)),
            _ => SpecPureFunctionArgument::ArrayRef {
                memory: self.memory(),
                pointer: self.expr(depth),
                element_type: CType::Int32,
            },
        }
    }

    fn seq(&mut self, depth: u32) -> SpecSequenceExpression {
        if depth == 0 || self.pick(2) == 0 {
            SpecSequenceExpression::Literal(vec![self.expr(depth), self.expr(depth)])
        } else {
            SpecSequenceExpression::Concat(
                Box::new(self.seq(depth - 1)),
                Box::new(self.seq(depth - 1)),
            )
        }
    }

    fn resource(&mut self, depth: u32) -> SpecResource {
        match self.pick(2) {
            0 => SpecResource::Memory {
                base: self.expr(depth),
                start: self.expr(depth),
                end: self.expr(depth),
                element_width: 4,
            },
            _ => SpecResource::Token {
                name: "t".into(),
                arguments: vec![self.expr(depth)],
            },
        }
    }

    fn prop(&mut self, depth: u32) -> SpecProposition {
        let d = depth.saturating_sub(1);
        let choice = if depth == 0 {
            self.pick(2)
        } else {
            self.pick(17)
        };
        match choice {
            0 => SpecProposition::Comparison {
                left: self.expr(d),
                operator: CComparisonOperator::LessThan,
                right: self.expr(d),
            },
            1 => SpecProposition::Defined(self.expr(d)),
            2 => SpecProposition::IntegerComparison {
                left: self.int(d),
                operator: IntegerComparisonOperator::LessEqual,
                right: self.int(d),
            },
            3 => SpecProposition::AlgebraicComparison {
                left: self.alg(d),
                equal: true,
                right: self.alg(d),
            },
            4 => SpecProposition::SequenceMembership {
                element: self.expr(d),
                sequence: self.seq(d),
            },
            5 => SpecProposition::SequenceComparison {
                left: self.seq(d),
                equal: false,
                right: self.seq(d),
            },
            6 => SpecProposition::And(Box::new(self.prop(d)), Box::new(self.prop(d))),
            7 => SpecProposition::Implies(Box::new(self.prop(d)), Box::new(self.prop(d))),
            8 => SpecProposition::Not(Box::new(self.prop(d))),
            9 => SpecProposition::ForAllInt32 {
                name: "k".into(),
                variable: Variable(900_020),
                body: Box::new(self.prop(d)),
            },
            10 => SpecProposition::ExistsInteger {
                name: "z".into(),
                variable: Variable(900_021),
                body: Box::new(self.prop(d)),
            },
            11 => SpecProposition::Predicate {
                name: "pred".into(),
                arguments: vec![
                    SpecPredicateArgument::Value(self.expr(d)),
                    SpecPredicateArgument::ArrayRef {
                        memory: self.memory(),
                        pointer: self.expr(d),
                    },
                ],
                resource_state_dependent: self.pick(2) == 0,
            },
            12 => SpecProposition::ResourceSeparate {
                left: self.resource(d),
                right: self.resource(d),
            },
            13 => SpecProposition::MemoryLoadable {
                memory: self.memory(),
                base: self.expr(d),
                start: self.expr(d),
                end: self.expr(d),
                element_width: 4,
            },
            14 => SpecProposition::FloatClassification {
                expression: self.expr(d),
                classification: CFloatClassification::Finite,
            },
            15 => SpecProposition::Or(Box::new(self.prop(d)), Box::new(self.prop(d))),
            _ => SpecProposition::ResourceContains {
                parent: self.resource(d),
                child: self.resource(d),
            },
        }
    }
}

/// The walk-based checks answer exactly as the recursive functions they
/// replaced did, on a few thousand mixed trees of every spec node kind.
fn old_spec_expression_reads_current_parameter(
    expression: &SpecExpression,
    parameter_name: &str,
) -> bool {
    match expression {
        SpecExpression::Value(_) | SpecExpression::ResourceField { .. } => false,
        SpecExpression::IntegerToMachine { value, .. } => {
            old_spec_integer_expression_reads_current_parameter(value, parameter_name)
        }
        SpecExpression::CExpression(expression) => {
            c_expression_mentions_variable(expression, parameter_name)
        }
        SpecExpression::AlgebraicMatch { scrutinee, arms } => {
            old_spec_algebraic_expression_reads_current_parameter(scrutinee, parameter_name)
                || arms.iter().any(|arm| {
                    old_spec_expression_reads_current_parameter(&arm.body, parameter_name)
                })
        }
        SpecExpression::CountedResourceCount { arguments, .. } => arguments
            .iter()
            .flatten()
            .any(|argument| old_spec_expression_reads_current_parameter(argument, parameter_name)),
        crate::kernel::binary_spec_expression!(left, right) => {
            old_spec_expression_reads_current_parameter(left, parameter_name)
                || old_spec_expression_reads_current_parameter(right, parameter_name)
        }
        SpecExpression::BitwiseNot(body)
        | SpecExpression::Cast(body, _)
        | SpecExpression::LoopEntrySnapshot(body) => {
            old_spec_expression_reads_current_parameter(body, parameter_name)
        }
        SpecExpression::If {
            condition,
            then_branch,
            else_branch,
        } => {
            old_spec_proposition_reads_current_parameter(condition, parameter_name)
                || old_spec_expression_reads_current_parameter(then_branch, parameter_name)
                || old_spec_expression_reads_current_parameter(else_branch, parameter_name)
        }
        SpecExpression::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        } => {
            old_spec_expression_reads_current_parameter(start, parameter_name)
                || old_spec_expression_reads_current_parameter(end, parameter_name)
                || old_spec_expression_reads_current_parameter(initial, parameter_name)
                || old_spec_expression_reads_current_parameter(body, parameter_name)
        }
        SpecExpression::Let { value, body, .. } => {
            old_spec_expression_reads_current_parameter(value, parameter_name)
                || old_spec_expression_reads_current_parameter(body, parameter_name)
        }
        SpecExpression::PureFunctionApplication { arguments, .. } => {
            arguments.iter().any(|argument| {
                old_spec_pure_function_argument_reads_current_parameter(argument, parameter_name)
            })
        }
        SpecExpression::PointerOffset {
            pointer, elements, ..
        } => {
            old_spec_expression_reads_current_parameter(pointer, parameter_name)
                || old_spec_expression_reads_current_parameter(elements, parameter_name)
        }
        SpecExpression::MemoryLoad {
            memory: SpecMemory::FunctionEntry | SpecMemory::Fixed(_),
            ..
        } => false,
        SpecExpression::AggregateFieldValue { pointer, .. }
        | SpecExpression::MemoryLoad { pointer, .. } => {
            old_spec_expression_reads_current_parameter(pointer, parameter_name)
        }
    }
}

fn old_spec_integer_expression_reads_current_parameter(
    expression: &SpecIntegerExpression,
    parameter_name: &str,
) -> bool {
    match expression {
        SpecIntegerExpression::Term(_) | SpecIntegerExpression::ResourceField(_) => false,
        SpecIntegerExpression::PureFunctionApplication { arguments, .. } => {
            arguments.iter().any(|argument| {
                old_spec_pure_function_argument_reads_current_parameter(argument, parameter_name)
            })
        }
        SpecIntegerExpression::AlgebraicMatch { scrutinee, arms } => {
            old_spec_algebraic_expression_reads_current_parameter(scrutinee, parameter_name)
                || arms.iter().any(|arm| {
                    old_spec_integer_expression_reads_current_parameter(&arm.body, parameter_name)
                })
        }
        SpecIntegerExpression::FromMachine(machine) => {
            old_spec_expression_reads_current_parameter(machine, parameter_name)
        }
        SpecIntegerExpression::Negate(inner) => {
            old_spec_integer_expression_reads_current_parameter(inner, parameter_name)
        }
        crate::kernel::binary_spec_integer_expression!(left, right) => {
            old_spec_integer_expression_reads_current_parameter(left, parameter_name)
                || old_spec_integer_expression_reads_current_parameter(right, parameter_name)
        }
        SpecIntegerExpression::RangeFold {
            index,
            initial,
            body,
            ..
        } => {
            let index_reads = match index {
                SpecIntegerRangeFoldIndex::Int32 { start, end }
                | SpecIntegerRangeFoldIndex::UInt64 { start, end } => {
                    old_spec_expression_reads_current_parameter(start, parameter_name)
                        || old_spec_expression_reads_current_parameter(end, parameter_name)
                }
                SpecIntegerRangeFoldIndex::Integer { start, end } => {
                    old_spec_integer_expression_reads_current_parameter(start, parameter_name)
                        || old_spec_integer_expression_reads_current_parameter(end, parameter_name)
                }
            };
            index_reads
                || old_spec_integer_expression_reads_current_parameter(initial, parameter_name)
                || old_spec_integer_expression_reads_current_parameter(body, parameter_name)
        }
    }
}

fn old_spec_proposition_reads_current_parameter(
    proposition: &SpecProposition,
    parameter_name: &str,
) -> bool {
    match proposition {
        SpecProposition::IntegerComparison { left, right, .. } => {
            old_spec_integer_expression_reads_current_parameter(left, parameter_name)
                || old_spec_integer_expression_reads_current_parameter(right, parameter_name)
        }
        SpecProposition::AlgebraicComparison { left, right, .. } => {
            old_spec_algebraic_expression_reads_current_parameter(left, parameter_name)
                || old_spec_algebraic_expression_reads_current_parameter(right, parameter_name)
        }
        SpecProposition::SequenceMembership { element, sequence } => {
            old_spec_expression_reads_current_parameter(element, parameter_name)
                || old_spec_sequence_reads_current_parameter(sequence, parameter_name)
        }
        SpecProposition::SequenceComparison { left, right, .. } => {
            old_spec_sequence_reads_current_parameter(left, parameter_name)
                || old_spec_sequence_reads_current_parameter(right, parameter_name)
        }
        SpecProposition::Comparison { left, right, .. } => {
            old_spec_expression_reads_current_parameter(left, parameter_name)
                || old_spec_expression_reads_current_parameter(right, parameter_name)
        }
        SpecProposition::FloatClassification { expression, .. }
        | SpecProposition::Defined(expression) => {
            old_spec_expression_reads_current_parameter(expression, parameter_name)
        }
        SpecProposition::And(left, right)
        | SpecProposition::Or(left, right)
        | SpecProposition::Implies(left, right) => {
            old_spec_proposition_reads_current_parameter(left, parameter_name)
                || old_spec_proposition_reads_current_parameter(right, parameter_name)
        }
        SpecProposition::Not(body)
        | SpecProposition::ForAllMachineInteger { body, .. }
        | SpecProposition::ForAllInt32 { body, .. }
        | SpecProposition::ForAllInteger { body, .. }
        | SpecProposition::ForAllAlgebraic { body, .. }
        | SpecProposition::ForAllPointer { body, .. }
        | SpecProposition::ExistsMachineInteger { body, .. }
        | SpecProposition::ExistsInt32 { body, .. }
        | SpecProposition::ExistsInteger { body, .. }
        | SpecProposition::ExistsAlgebraic { body, .. }
        | SpecProposition::ExistsPointer { body, .. } => {
            old_spec_proposition_reads_current_parameter(body, parameter_name)
        }
        SpecProposition::Predicate { arguments, .. } => {
            arguments.iter().any(|argument| match argument {
                SpecPredicateArgument::Value(expression) => {
                    old_spec_expression_reads_current_parameter(expression, parameter_name)
                }
                SpecPredicateArgument::ArrayRef { memory, pointer } => {
                    !matches!(memory, SpecMemory::FunctionEntry | SpecMemory::Fixed(_))
                        && old_spec_expression_reads_current_parameter(pointer, parameter_name)
                }
            })
        }
        SpecProposition::ResourceSeparate { left, right }
        | SpecProposition::ResourceContains {
            parent: left,
            child: right,
        } => {
            old_spec_resource_reads_current_parameter(left, parameter_name)
                || old_spec_resource_reads_current_parameter(right, parameter_name)
        }
        SpecProposition::MemoryLoadable {
            memory,
            base,
            start,
            end,
            ..
        } => {
            !matches!(memory, SpecMemory::FunctionEntry | SpecMemory::Fixed(_))
                && (old_spec_expression_reads_current_parameter(base, parameter_name)
                    || old_spec_expression_reads_current_parameter(start, parameter_name)
                    || old_spec_expression_reads_current_parameter(end, parameter_name))
        }
    }
}

fn old_spec_sequence_reads_current_parameter(
    sequence: &SpecSequenceExpression,
    parameter_name: &str,
) -> bool {
    match sequence {
        SpecSequenceExpression::Literal(elements) => elements
            .iter()
            .any(|element| old_spec_expression_reads_current_parameter(element, parameter_name)),
        SpecSequenceExpression::Concat(left, right) => {
            old_spec_sequence_reads_current_parameter(left, parameter_name)
                || old_spec_sequence_reads_current_parameter(right, parameter_name)
        }
    }
}

fn old_spec_resource_reads_current_parameter(
    resource: &SpecResource,
    parameter_name: &str,
) -> bool {
    match resource {
        SpecResource::Memory {
            base, start, end, ..
        } => {
            old_spec_expression_reads_current_parameter(base, parameter_name)
                || old_spec_expression_reads_current_parameter(start, parameter_name)
                || old_spec_expression_reads_current_parameter(end, parameter_name)
        }
        SpecResource::Composite { arguments, .. } | SpecResource::Token { arguments, .. } => {
            arguments.iter().any(|argument| {
                old_spec_expression_reads_current_parameter(argument, parameter_name)
            })
        }
    }
}

fn old_spec_algebraic_expression_reads_current_parameter(
    expression: &SpecAlgebraicExpression,
    parameter_name: &str,
) -> bool {
    match &expression.node {
        SpecAlgebraicExpressionNode::Variable(_)
        | SpecAlgebraicExpressionNode::Binding(_)
        | SpecAlgebraicExpressionNode::ResourceField(_) => false,
        SpecAlgebraicExpressionNode::Constructor { fields, .. } => {
            fields.iter().any(|field| match field {
                SpecAlgebraicValue::C(expression) => {
                    old_spec_expression_reads_current_parameter(expression, parameter_name)
                }
                SpecAlgebraicValue::Integer(expression) => {
                    old_spec_integer_expression_reads_current_parameter(expression, parameter_name)
                }
                SpecAlgebraicValue::Algebraic(expression) => {
                    old_spec_algebraic_expression_reads_current_parameter(
                        expression,
                        parameter_name,
                    )
                }
            })
        }
        SpecAlgebraicExpressionNode::Match { scrutinee, arms } => {
            old_spec_algebraic_expression_reads_current_parameter(scrutinee, parameter_name)
                || arms.iter().any(|arm| {
                    old_spec_algebraic_expression_reads_current_parameter(&arm.body, parameter_name)
                })
        }
        SpecAlgebraicExpressionNode::PureFunctionApplication { arguments, .. } => {
            arguments.iter().any(|argument| {
                old_spec_pure_function_argument_reads_current_parameter(argument, parameter_name)
            })
        }
    }
}

fn old_spec_pure_function_argument_reads_current_parameter(
    argument: &SpecPureFunctionArgument,
    parameter_name: &str,
) -> bool {
    match argument {
        SpecPureFunctionArgument::Value(expression) => {
            old_spec_expression_reads_current_parameter(expression, parameter_name)
        }
        SpecPureFunctionArgument::Integer(expression) => {
            old_spec_integer_expression_reads_current_parameter(expression, parameter_name)
        }
        SpecPureFunctionArgument::Algebraic(expression) => {
            old_spec_algebraic_expression_reads_current_parameter(expression, parameter_name)
        }
        SpecPureFunctionArgument::ArrayRef {
            memory, pointer, ..
        } => {
            !matches!(memory, SpecMemory::FunctionEntry | SpecMemory::Fixed(_))
                && old_spec_expression_reads_current_parameter(pointer, parameter_name)
        }
    }
}

fn old_spec_expression_current_parameter_accesses(
    expression: &SpecExpression,
    parameter_name: &str,
    reads: &mut Vec<ParameterAccessRange>,
    unknown_read: &mut bool,
) {
    match expression {
        SpecExpression::Value(_) | SpecExpression::ResourceField { .. } => {}
        SpecExpression::IntegerToMachine { .. } => *unknown_read = true,
        SpecExpression::CExpression(expression) => {
            if c_expression_mentions_variable(expression, parameter_name) {
                *unknown_read = true;
            }
        }
        SpecExpression::AlgebraicMatch { scrutinee, arms } => {
            old_spec_algebraic_expression_current_parameter_accesses(
                scrutinee,
                parameter_name,
                reads,
                unknown_read,
            );
            for arm in arms {
                old_spec_expression_current_parameter_accesses(
                    &arm.body,
                    parameter_name,
                    reads,
                    unknown_read,
                );
            }
        }
        SpecExpression::CountedResourceCount { arguments, .. } => {
            for argument in arguments.iter().flatten() {
                old_spec_expression_current_parameter_accesses(
                    argument,
                    parameter_name,
                    reads,
                    unknown_read,
                );
            }
        }
        crate::kernel::binary_spec_expression!(left, right) => {
            old_spec_expression_current_parameter_accesses(
                left,
                parameter_name,
                reads,
                unknown_read,
            );
            old_spec_expression_current_parameter_accesses(
                right,
                parameter_name,
                reads,
                unknown_read,
            );
        }
        SpecExpression::BitwiseNot(body)
        | SpecExpression::Cast(body, _)
        | SpecExpression::LoopEntrySnapshot(body) => {
            old_spec_expression_current_parameter_accesses(
                body,
                parameter_name,
                reads,
                unknown_read,
            );
        }
        SpecExpression::If {
            condition,
            then_branch,
            else_branch,
        } => {
            old_spec_proposition_current_parameter_accesses(
                condition,
                parameter_name,
                reads,
                unknown_read,
            );
            old_spec_expression_current_parameter_accesses(
                then_branch,
                parameter_name,
                reads,
                unknown_read,
            );
            old_spec_expression_current_parameter_accesses(
                else_branch,
                parameter_name,
                reads,
                unknown_read,
            );
        }
        SpecExpression::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        } => {
            old_spec_expression_current_parameter_accesses(
                start,
                parameter_name,
                reads,
                unknown_read,
            );
            old_spec_expression_current_parameter_accesses(
                end,
                parameter_name,
                reads,
                unknown_read,
            );
            old_spec_expression_current_parameter_accesses(
                initial,
                parameter_name,
                reads,
                unknown_read,
            );
            old_spec_expression_current_parameter_accesses(
                body,
                parameter_name,
                reads,
                unknown_read,
            );
        }
        SpecExpression::Let { value, body, .. } => {
            old_spec_expression_current_parameter_accesses(
                value,
                parameter_name,
                reads,
                unknown_read,
            );
            old_spec_expression_current_parameter_accesses(
                body,
                parameter_name,
                reads,
                unknown_read,
            );
        }
        SpecExpression::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                old_spec_pure_function_argument_current_parameter_accesses(
                    argument,
                    parameter_name,
                    reads,
                    unknown_read,
                );
            }
        }
        SpecExpression::PointerOffset {
            pointer, elements, ..
        } => {
            old_spec_expression_current_parameter_accesses(
                pointer,
                parameter_name,
                reads,
                unknown_read,
            );
            old_spec_expression_current_parameter_accesses(
                elements,
                parameter_name,
                reads,
                unknown_read,
            );
        }
        SpecExpression::MemoryLoad {
            memory: SpecMemory::FunctionEntry | SpecMemory::Fixed(_),
            ..
        } => {}
        SpecExpression::AggregateFieldValue {
            pointer,
            value_type,
            ..
        }
        | SpecExpression::MemoryLoad {
            memory: SpecMemory::Current,
            pointer,
            value_type,
        } => {
            if let Some(offset) = spec_expression_parameter_offset(pointer, parameter_name) {
                if let Some(range) = parameter_access_range(offset, value_type.byte_width()) {
                    reads.push(range);
                }
            } else if old_spec_expression_reads_current_parameter(pointer, parameter_name) {
                *unknown_read = true;
            }
        }
        SpecExpression::MemoryLoad {
            memory: SpecMemory::LoopEntry,
            pointer,
            ..
        } => {
            if old_spec_expression_reads_current_parameter(pointer, parameter_name) {
                *unknown_read = true;
            }
        }
    }
}

fn old_spec_proposition_current_parameter_accesses(
    proposition: &SpecProposition,
    parameter_name: &str,
    reads: &mut Vec<ParameterAccessRange>,
    unknown_read: &mut bool,
) {
    match proposition {
        // An Integer read has no precise byte range here, so any read of the
        // parameter is an unknown read.
        SpecProposition::IntegerComparison { left, right, .. } => {
            *unknown_read |=
                old_spec_integer_expression_reads_current_parameter(left, parameter_name)
                    || old_spec_integer_expression_reads_current_parameter(right, parameter_name);
        }
        SpecProposition::AlgebraicComparison { left, right, .. } => {
            old_spec_algebraic_expression_current_parameter_accesses(
                left,
                parameter_name,
                reads,
                unknown_read,
            );
            old_spec_algebraic_expression_current_parameter_accesses(
                right,
                parameter_name,
                reads,
                unknown_read,
            );
        }
        SpecProposition::SequenceMembership { element, sequence } => {
            old_spec_expression_current_parameter_accesses(
                element,
                parameter_name,
                reads,
                unknown_read,
            );
            old_spec_sequence_current_parameter_accesses(
                sequence,
                parameter_name,
                reads,
                unknown_read,
            );
        }
        SpecProposition::SequenceComparison { left, right, .. } => {
            old_spec_sequence_current_parameter_accesses(left, parameter_name, reads, unknown_read);
            old_spec_sequence_current_parameter_accesses(
                right,
                parameter_name,
                reads,
                unknown_read,
            );
        }
        SpecProposition::Comparison { left, right, .. } => {
            old_spec_expression_current_parameter_accesses(
                left,
                parameter_name,
                reads,
                unknown_read,
            );
            old_spec_expression_current_parameter_accesses(
                right,
                parameter_name,
                reads,
                unknown_read,
            );
        }
        SpecProposition::FloatClassification { expression, .. }
        | SpecProposition::Defined(expression) => {
            old_spec_expression_current_parameter_accesses(
                expression,
                parameter_name,
                reads,
                unknown_read,
            );
        }
        SpecProposition::And(left, right)
        | SpecProposition::Or(left, right)
        | SpecProposition::Implies(left, right) => {
            old_spec_proposition_current_parameter_accesses(
                left,
                parameter_name,
                reads,
                unknown_read,
            );
            old_spec_proposition_current_parameter_accesses(
                right,
                parameter_name,
                reads,
                unknown_read,
            );
        }
        SpecProposition::Not(body)
        | SpecProposition::ForAllMachineInteger { body, .. }
        | SpecProposition::ForAllInt32 { body, .. }
        | SpecProposition::ForAllInteger { body, .. }
        | SpecProposition::ForAllAlgebraic { body, .. }
        | SpecProposition::ForAllPointer { body, .. }
        | SpecProposition::ExistsMachineInteger { body, .. }
        | SpecProposition::ExistsInt32 { body, .. }
        | SpecProposition::ExistsInteger { body, .. }
        | SpecProposition::ExistsAlgebraic { body, .. }
        | SpecProposition::ExistsPointer { body, .. } => {
            old_spec_proposition_current_parameter_accesses(
                body,
                parameter_name,
                reads,
                unknown_read,
            );
        }
        SpecProposition::Predicate { arguments, .. } => {
            for argument in arguments {
                match argument {
                    SpecPredicateArgument::Value(expression) => {
                        old_spec_expression_current_parameter_accesses(
                            expression,
                            parameter_name,
                            reads,
                            unknown_read,
                        );
                    }
                    SpecPredicateArgument::ArrayRef { memory, pointer } => {
                        if !matches!(memory, SpecMemory::FunctionEntry | SpecMemory::Fixed(_))
                            && old_spec_expression_reads_current_parameter(pointer, parameter_name)
                        {
                            *unknown_read = true;
                        }
                    }
                }
            }
        }
        SpecProposition::ResourceSeparate { left, right }
        | SpecProposition::ResourceContains {
            parent: left,
            child: right,
        } => {
            old_spec_resource_current_parameter_accesses(left, parameter_name, reads, unknown_read);
            old_spec_resource_current_parameter_accesses(
                right,
                parameter_name,
                reads,
                unknown_read,
            );
        }
        SpecProposition::MemoryLoadable {
            memory,
            base,
            start,
            end,
            ..
        } => {
            if !matches!(memory, SpecMemory::FunctionEntry | SpecMemory::Fixed(_))
                && (old_spec_expression_reads_current_parameter(base, parameter_name)
                    || old_spec_expression_reads_current_parameter(start, parameter_name)
                    || old_spec_expression_reads_current_parameter(end, parameter_name))
            {
                *unknown_read = true;
            }
        }
    }
}

fn old_spec_sequence_current_parameter_accesses(
    sequence: &SpecSequenceExpression,
    parameter_name: &str,
    reads: &mut Vec<ParameterAccessRange>,
    unknown_read: &mut bool,
) {
    match sequence {
        SpecSequenceExpression::Literal(elements) => {
            for element in elements {
                old_spec_expression_current_parameter_accesses(
                    element,
                    parameter_name,
                    reads,
                    unknown_read,
                );
            }
        }
        SpecSequenceExpression::Concat(left, right) => {
            old_spec_sequence_current_parameter_accesses(left, parameter_name, reads, unknown_read);
            old_spec_sequence_current_parameter_accesses(
                right,
                parameter_name,
                reads,
                unknown_read,
            );
        }
    }
}

fn old_spec_resource_current_parameter_accesses(
    resource: &SpecResource,
    parameter_name: &str,
    reads: &mut Vec<ParameterAccessRange>,
    unknown_read: &mut bool,
) {
    match resource {
        SpecResource::Memory {
            base, start, end, ..
        } => {
            if old_spec_expression_reads_current_parameter(base, parameter_name)
                || old_spec_expression_reads_current_parameter(start, parameter_name)
                || old_spec_expression_reads_current_parameter(end, parameter_name)
            {
                *unknown_read = true;
            }
        }
        SpecResource::Composite { arguments, .. } | SpecResource::Token { arguments, .. } => {
            for argument in arguments {
                old_spec_expression_current_parameter_accesses(
                    argument,
                    parameter_name,
                    reads,
                    unknown_read,
                );
            }
        }
    }
}

fn old_spec_algebraic_expression_current_parameter_accesses(
    expression: &SpecAlgebraicExpression,
    parameter_name: &str,
    reads: &mut Vec<ParameterAccessRange>,
    unknown_read: &mut bool,
) {
    match &expression.node {
        SpecAlgebraicExpressionNode::Variable(_)
        | SpecAlgebraicExpressionNode::Binding(_)
        | SpecAlgebraicExpressionNode::ResourceField(_) => {}
        SpecAlgebraicExpressionNode::Constructor { fields, .. } => {
            for field in fields {
                match field {
                    SpecAlgebraicValue::C(expression) => {
                        old_spec_expression_current_parameter_accesses(
                            expression,
                            parameter_name,
                            reads,
                            unknown_read,
                        );
                    }
                    SpecAlgebraicValue::Integer(expression) => {
                        *unknown_read |= old_spec_integer_expression_reads_current_parameter(
                            expression,
                            parameter_name,
                        );
                    }
                    SpecAlgebraicValue::Algebraic(expression) => {
                        old_spec_algebraic_expression_current_parameter_accesses(
                            expression,
                            parameter_name,
                            reads,
                            unknown_read,
                        );
                    }
                }
            }
        }
        SpecAlgebraicExpressionNode::Match { scrutinee, arms } => {
            old_spec_algebraic_expression_current_parameter_accesses(
                scrutinee,
                parameter_name,
                reads,
                unknown_read,
            );
            for arm in arms {
                old_spec_algebraic_expression_current_parameter_accesses(
                    &arm.body,
                    parameter_name,
                    reads,
                    unknown_read,
                );
            }
        }
        SpecAlgebraicExpressionNode::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                old_spec_pure_function_argument_current_parameter_accesses(
                    argument,
                    parameter_name,
                    reads,
                    unknown_read,
                );
            }
        }
    }
}

fn old_spec_pure_function_argument_current_parameter_accesses(
    argument: &SpecPureFunctionArgument,
    parameter_name: &str,
    reads: &mut Vec<ParameterAccessRange>,
    unknown_read: &mut bool,
) {
    match argument {
        SpecPureFunctionArgument::Value(expression) => {
            old_spec_expression_current_parameter_accesses(
                expression,
                parameter_name,
                reads,
                unknown_read,
            );
        }
        SpecPureFunctionArgument::Integer(expression) => {
            *unknown_read |=
                old_spec_integer_expression_reads_current_parameter(expression, parameter_name);
        }
        SpecPureFunctionArgument::Algebraic(expression) => {
            old_spec_algebraic_expression_current_parameter_accesses(
                expression,
                parameter_name,
                reads,
                unknown_read,
            );
        }
        SpecPureFunctionArgument::ArrayRef {
            memory, pointer, ..
        } => {
            if !matches!(memory, SpecMemory::FunctionEntry | SpecMemory::Fixed(_))
                && old_spec_expression_reads_current_parameter(pointer, parameter_name)
            {
                *unknown_read = true;
            }
        }
    }
}

#[test]
fn spec_walk_families_agree_with_their_recursive_originals() {
    let mut generator = Gen(0x9e37_79b9_7f4a_7c15);
    let (mut independent, mut stateful, mut observing) = (0, 0, 0);
    let (mut reading, mut ranged, mut unknown) = (0, 0, 0);
    for round in 0..4000 {
        let depth = 1 + (round % 5) as u32;
        let proposition = generator.prop(depth);
        let old = old_spec_proposition_is_state_independent(&proposition);
        assert_eq!(
            spec_proposition_is_state_independent(&proposition),
            old,
            "{proposition:?}"
        );
        independent += usize::from(old);
        let old = old_spec_proposition_supports_stateful_memory_refinement(&proposition);
        assert_eq!(
            spec_proposition_supports_stateful_memory_refinement(&proposition),
            old,
            "{proposition:?}"
        );
        stateful += usize::from(old);
        let old = old_observes_resource_state(&proposition);
        assert_eq!(
            super::super::spec::predicate_dependencies::observes_resource_state(&proposition),
            old,
            "{proposition:?}"
        );
        observing += usize::from(old);
        let old = old_spec_proposition_reads_current_parameter(&proposition, "x");
        assert_eq!(
            spec_reads_current_parameter(SpecNode::Proposition(&proposition), "x"),
            old,
            "{proposition:?}"
        );
        reading += usize::from(old);
        let (mut old_reads, mut old_unknown) = (Vec::new(), false);
        old_spec_proposition_current_parameter_accesses(
            &proposition,
            "x",
            &mut old_reads,
            &mut old_unknown,
        );
        let (mut reads, mut unknown_read) = (Vec::new(), false);
        spec_proposition_current_parameter_accesses(
            &proposition,
            "x",
            &mut reads,
            &mut unknown_read,
        );
        assert_eq!(
            (reads, unknown_read),
            (old_reads.clone(), old_unknown),
            "{proposition:?}"
        );
        ranged += usize::from(!old_reads.is_empty());
        unknown += usize::from(old_unknown);
        let algebraic = generator.alg(depth);
        assert_eq!(
            spec_algebraic_expression_is_state_independent(&algebraic),
            old_spec_algebraic_expression_is_state_independent(&algebraic),
            "{algebraic:?}"
        );
        assert_eq!(
            spec_algebraic_expression_is_obligation_free(&algebraic),
            old_spec_algebraic_expression_is_obligation_free(&algebraic),
            "{algebraic:?}"
        );
    }
    // Both answers occur often enough for the comparison to mean something.
    for count in [independent, stateful, observing, reading, ranged, unknown] {
        assert!(
            (200..3800).contains(&count),
            "{independent} {stateful} {observing} {reading} {ranged} {unknown}"
        );
    }
}
