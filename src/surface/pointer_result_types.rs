//! Pointer origins of pure results, computed once from the definition bodies.
//! This is a transfer of existing evidence, not a refinement inferred from a
//! return declaration. Unsupported expressions and recursive cycles stay opaque.

use super::*;
use crate::kernel::PurePointerResult;
use crate::kernel::effective_type::{CAccessClass, CPointeeBase, CStructClass};
use std::sync::Arc;

type Origins = Option<Arc<PurePointerResult>>;

impl FunctionParameter {
    pub(super) fn pointer_object_class(&self) -> Option<CAccessClass> {
        struct_pointer_class(self.click_type().c_type()?, self.struct_name()?)
    }
}

fn struct_pointer_class(c_type: C0Type, name: &str) -> Option<CAccessClass> {
    let pointee = c_type.pointee_type()?;
    let class = CStructClass::opaque(name.to_string());
    Some(if pointee.is_pointer() {
        CAccessClass::Pointer {
            base: CPointeeBase::Struct(class),
            depth: 1,
        }
    } else {
        CAccessClass::Struct(class)
    })
}

impl AlgebraicFieldType {
    pub(super) fn pointer_object_class(&self) -> Option<CAccessClass> {
        let Self::C {
            c_type,
            struct_name: Some(name),
            ..
        } = self
        else {
            return None;
        };
        struct_pointer_class(*c_type, name)
    }
}

fn null_origins() -> Arc<PurePointerResult> {
    Arc::new(PurePointerResult {
        classes: BTreeSet::new(),
        arguments: BTreeSet::new(),
    })
}

fn merge(into: &mut PurePointerResult, other: &PurePointerResult) {
    into.classes.extend(other.classes.iter().cloned());
    into.arguments.extend(other.arguments.iter().copied());
}

struct Analysis<'a> {
    functions: BTreeMap<&'a str, &'a ClickFunctionDefinition>,
    models: BTreeMap<&'a str, &'a AlgebraicTypeDefinition>,
    results: BTreeMap<String, Origins>,
    active: BTreeSet<String>,
    expressions: BTreeMap<usize, Origins>,
}

pub(super) fn pointer_result_types(
    definitions: &[ClickFunctionDefinition],
    models: &[AlgebraicTypeDefinition],
) -> (BTreeMap<String, Origins>, Option<(String, String)>) {
    let mut analysis = Analysis {
        functions: definitions.iter().map(|d| (d.name(), d)).collect(),
        models: models.iter().map(|d| (d.name(), d)).collect(),
        results: BTreeMap::new(),
        active: BTreeSet::new(),
        expressions: BTreeMap::new(),
    };
    for definition in definitions {
        analysis.function(definition.name());
    }
    let error = definitions.iter().find_map(|definition| {
        analysis
            .check_definition(definition)
            .err()
            .map(|error| (definition.name().to_string(), error))
    });
    (analysis.results, error)
}

impl Analysis<'_> {
    fn function(&mut self, name: &str) -> Origins {
        let name = generic_instance_source_name(name);
        if let Some(result) = self.results.get(name) {
            return result.clone();
        }
        let definition = *self.functions.get(name)?;
        if !(matches!(definition.return_type(), ClickType::C(ty) if ty.is_object_pointer())
            || matches!(definition.return_type(), ClickType::Parameter(_)))
            || !self.active.insert(name.to_string())
        {
            return None;
        }
        let mut bindings = definition
            .parameters()
            .iter()
            .enumerate()
            .map(|(index, parameter)| {
                let origin =
                    (matches!(parameter.click_type(), ClickType::C(ty) if ty.is_object_pointer())
                        || matches!(parameter.click_type(), ClickType::Parameter(_)))
                    .then(|| {
                        Arc::new(PurePointerResult {
                            classes: BTreeSet::new(),
                            arguments: BTreeSet::from([index]),
                        })
                    });
                (parameter.name().to_string(), origin)
            })
            .collect();
        let result = self.expression(definition.body(), &mut bindings);
        self.active.remove(name);
        self.results.insert(name.to_string(), result.clone());
        result
    }

    fn c_expression(expression: &CExpression, bindings: &BTreeMap<String, Origins>) -> Origins {
        match expression {
            CExpression::Variable(name) => bindings.get(name).cloned().flatten(),
            CExpression::Value(CValue::Pointer(p)) if p.is_null() => Some(null_origins()),
            CExpression::Value(CValue::Int32(bits)) if bits.as_const() == Some(0) => {
                Some(null_origins())
            }
            CExpression::Cast {
                expression,
                target_type,
                ..
            } if target_type.is_pointer() => Self::c_expression(expression, bindings),
            _ => None,
        }
    }

    fn expression(
        &mut self,
        expression: &ContractExpression,
        bindings: &mut BTreeMap<String, Origins>,
    ) -> Origins {
        // One lexical context per source expression. Reusing the origin when
        // validating enclosing calls avoids revisiting nested argument trees.
        let key = expression as *const ContractExpression as usize;
        if let Some(origin) = self.expressions.get(&key) {
            return origin.clone();
        }
        crate::instrumentation::record_deterministic_work(1);
        let result = self.expression_inner(expression, bindings);
        self.expressions.insert(key, result.clone());
        result
    }

    fn expression_inner(
        &mut self,
        expression: &ContractExpression,
        bindings: &mut BTreeMap<String, Origins>,
    ) -> Origins {
        match expression {
            ContractExpression::IntegerLiteral(value) if value == "0" => Some(null_origins()),
            ContractExpression::Binding(name) | ContractExpression::CBinding(name) => {
                bindings.get(name).cloned().flatten()
            }
            ContractExpression::CFragment(expression) => Self::c_expression(expression, bindings),
            ContractExpression::CUnary {
                operand,
                lowered: CExpression::Cast { target_type, .. },
            } if target_type.is_object_pointer() => self.expression(operand, bindings),
            ContractExpression::If {
                then_branch,
                else_branch,
                ..
            } => {
                let mut result = (*self.expression(then_branch, bindings)?).clone();
                merge(
                    &mut result,
                    self.expression(else_branch, bindings)?.as_ref(),
                );
                Some(Arc::new(result))
            }
            ContractExpression::Let {
                name, value, body, ..
            } => {
                let value = self.expression(value, bindings);
                let previous = bindings.insert(name.clone(), value);
                let result = self.expression(body, bindings);
                restore(bindings, name, previous);
                result
            }
            ContractExpression::AlgebraicMatch { arms, .. } => {
                let mut result = (*null_origins()).clone();
                for arm in arms {
                    let model = *self.models.get(arm.type_name.as_str())?;
                    let variant = model.variants().iter().find(|v| v.name() == arm.variant)?;
                    if variant.fields().len() != arm.bindings.len() {
                        return None;
                    }
                    let mut previous = Vec::new();
                    for (name, field) in arm.bindings.iter().zip(variant.fields()) {
                        let origin = field.pointer_object_class().map(|class| {
                            Arc::new(PurePointerResult {
                                classes: BTreeSet::from([class]),
                                arguments: BTreeSet::new(),
                            })
                        });
                        previous.push((name, bindings.insert(name.clone(), origin)));
                    }
                    let origin = self.expression(&arm.body, bindings);
                    for (name, previous) in previous.into_iter().rev() {
                        restore(bindings, name, previous);
                    }
                    merge(&mut result, origin?.as_ref());
                }
                (!arms.is_empty()).then(|| Arc::new(result))
            }
            ContractExpression::Call { name, arguments } => {
                let callee = self.function(name)?;
                let mut result = PurePointerResult {
                    classes: callee.classes.clone(),
                    arguments: BTreeSet::new(),
                };
                for index in &callee.arguments {
                    merge(
                        &mut result,
                        self.expression(arguments.get(*index)?, bindings)?.as_ref(),
                    );
                }
                Some(Arc::new(result))
            }
            _ => None,
        }
    }
}

fn restore(bindings: &mut BTreeMap<String, Origins>, name: &str, previous: Option<Origins>) {
    if let Some(previous) = previous {
        bindings.insert(name.to_string(), previous);
    } else {
        bindings.remove(name);
    }
}

impl Analysis<'_> {
    fn check_definition(&mut self, definition: &ClickFunctionDefinition) -> Result<(), String> {
        let mut bindings = definition
            .parameters()
            .iter()
            .enumerate()
            .map(|(index, parameter)| {
                let origin =
                    (matches!(parameter.click_type(), ClickType::C(ty) if ty.is_object_pointer())
                        || matches!(parameter.click_type(), ClickType::Parameter(_)))
                    .then(|| {
                        Arc::new(PurePointerResult {
                            classes: BTreeSet::new(),
                            arguments: BTreeSet::from([index]),
                        })
                    });
                (parameter.name().to_string(), origin)
            })
            .collect();
        self.check_expression(definition.body(), &mut bindings, definition)
    }

    fn require_class(
        &mut self,
        expression: &ContractExpression,
        class: &CAccessClass,
        bindings: &mut BTreeMap<String, Origins>,
        definition: &ClickFunctionDefinition,
        place: &str,
    ) -> Result<(), String> {
        let valid = self
            .expression(expression, bindings)
            .is_some_and(|origins| {
                origins.classes.iter().all(|origin| origin == class)
                    && origins.arguments.iter().all(|index| {
                        definition
                            .parameters()
                            .get(*index)
                            .and_then(FunctionParameter::pointer_object_class)
                            .as_ref()
                            == Some(class)
                    })
            });
        if valid {
            Ok(())
        } else {
            Err(format!(
                "function `{}` {place} requires original object class `{class}` or null",
                definition.name()
            ))
        }
    }

    fn check_expression(
        &mut self,
        expression: &ContractExpression,
        bindings: &mut BTreeMap<String, Origins>,
        definition: &ClickFunctionDefinition,
    ) -> Result<(), String> {
        crate::instrumentation::record_deterministic_work(1);
        match expression {
            ContractExpression::AlgebraicConstructor {
                algebraic_type,
                variant,
                arguments,
            } => {
                if let Some(model) = self.models.get(algebraic_type.name.as_str()).copied()
                    && let Some(schema) = model.variants().iter().find(|v| v.name() == variant)
                {
                    for (index, (field, argument)) in
                        schema.fields().iter().zip(arguments).enumerate()
                    {
                        if let Some(class) = field.pointer_object_class() {
                            self.require_class(
                                argument,
                                &class,
                                bindings,
                                definition,
                                &format!(
                                    "constructor `{}::{variant}` argument {index}",
                                    model.name()
                                ),
                            )?;
                        }
                    }
                }
                for argument in arguments {
                    self.check_expression(argument, bindings, definition)?;
                }
            }
            ContractExpression::Call { name, arguments } => {
                if let Some(callee) = self
                    .functions
                    .get(generic_instance_source_name(name))
                    .copied()
                {
                    for (parameter, argument) in callee.parameters().iter().zip(arguments) {
                        if let Some(class) = parameter.pointer_object_class() {
                            self.require_class(
                                argument,
                                &class,
                                bindings,
                                definition,
                                &format!("call `{name}` parameter `{}`", parameter.name()),
                            )?;
                        }
                    }
                }
                for argument in arguments {
                    self.check_expression(argument, bindings, definition)?;
                }
            }
            ContractExpression::AlgebraicMatch { scrutinee, arms } => {
                self.check_expression(scrutinee, bindings, definition)?;
                for arm in arms {
                    let fields = self
                        .models
                        .get(arm.type_name.as_str())
                        .and_then(|model| model.variants().iter().find(|v| v.name() == arm.variant))
                        .map(|variant| variant.fields())
                        .unwrap_or_default();
                    let mut previous = Vec::new();
                    for (index, name) in arm.bindings.iter().enumerate() {
                        let origin = fields
                            .get(index)
                            .and_then(AlgebraicFieldType::pointer_object_class)
                            .map(|class| {
                                Arc::new(PurePointerResult {
                                    classes: BTreeSet::from([class]),
                                    arguments: BTreeSet::new(),
                                })
                            });
                        previous.push((name, bindings.insert(name.clone(), origin)));
                    }
                    let checked = self.check_expression(&arm.body, bindings, definition);
                    for (name, previous) in previous.into_iter().rev() {
                        restore(bindings, name, previous);
                    }
                    checked?;
                }
            }
            ContractExpression::Let {
                name, value, body, ..
            } => {
                self.check_expression(value, bindings, definition)?;
                let origin = self.expression(value, bindings);
                let previous = bindings.insert(name.clone(), origin);
                let checked = self.check_expression(body, bindings, definition);
                restore(bindings, name, previous);
                checked?;
            }
            ContractExpression::If {
                condition,
                then_branch,
                else_branch,
            } => {
                self.check_proposition(condition, bindings, definition)?;
                self.check_expression(then_branch, bindings, definition)?;
                self.check_expression(else_branch, bindings, definition)?;
            }
            ContractExpression::RangeFold {
                start,
                end,
                initial,
                accumulator,
                item,
                body,
            } => {
                for value in [start, end, initial] {
                    self.check_expression(value, bindings, definition)?;
                }
                // The accumulator may change at every iteration: the initial
                // pointer's origin alone cannot give its body's origin.
                let old_accumulator = bindings.insert(accumulator.clone(), None);
                let old_item = bindings.insert(item.clone(), None);
                let checked = self.check_expression(body, bindings, definition);
                restore(bindings, item, old_item);
                restore(bindings, accumulator, old_accumulator);
                checked?;
            }
            ContractExpression::CUnary { operand: inner, .. }
            | ContractExpression::Negate(inner)
            | ContractExpression::BitwiseNot(inner)
            | ContractExpression::Old(inner)
            | ContractExpression::At {
                expression: inner, ..
            }
            | ContractExpression::Field { base: inner, .. } => {
                self.check_expression(inner, bindings, definition)?;
            }
            binary_contract_expression!(left, right)
            | ContractExpression::SequenceConcat(left, right) => {
                self.check_expression(left, bindings, definition)?;
                self.check_expression(right, bindings, definition)?;
            }
            ContractExpression::SequenceLiteral(values) => {
                for value in values {
                    self.check_expression(value, bindings, definition)?;
                }
            }
            ContractExpression::ArrayIndex { base, indexes, .. } => {
                self.check_expression(base, bindings, definition)?;
                for index in indexes {
                    self.check_expression(index, bindings, definition)?;
                }
            }
            ContractExpression::ResourceCount(resource) => {
                if let ResourceClause::Declared { arguments, .. } = resource.as_ref() {
                    for argument in arguments {
                        self.check_expression(argument, bindings, definition)?;
                    }
                }
            }
            ContractExpression::IntegerLiteral(_)
            | ContractExpression::QualifiedC { .. }
            | ContractExpression::ResourceField(_)
            | ContractExpression::ResourceWildcard
            | ContractExpression::AlgebraicVariable { .. }
            | ContractExpression::Binding(_)
            | ContractExpression::CBinding(_)
            | ContractExpression::CFragment(_) => {}
        }
        Ok(())
    }

    fn check_proposition(
        &mut self,
        proposition: &ClickProposition,
        bindings: &mut BTreeMap<String, Origins>,
        definition: &ClickFunctionDefinition,
    ) -> Result<(), String> {
        match proposition {
            ClickProposition::Comparison { left, right, .. } => {
                self.check_expression(left, bindings, definition)?;
                self.check_expression(right, bindings, definition)?;
            }
            ClickProposition::FloatClassification { expression, .. }
            | ClickProposition::Defined { expression } => {
                self.check_expression(expression, bindings, definition)?;
            }
            ClickProposition::PredicateCall { arguments, .. } => {
                for argument in arguments {
                    self.check_expression(argument, bindings, definition)?;
                }
            }
            ClickProposition::And(left, right)
            | ClickProposition::Or(left, right)
            | ClickProposition::Implies(left, right) => {
                self.check_proposition(left, bindings, definition)?;
                self.check_proposition(right, bindings, definition)?;
            }
            ClickProposition::Not(body)
            | ClickProposition::At {
                proposition: body, ..
            } => {
                self.check_proposition(body, bindings, definition)?;
            }
            ClickProposition::ForAll { name, body, .. }
            | ClickProposition::Exists { name, body, .. } => {
                let previous = bindings.insert(name.clone(), None);
                let checked = self.check_proposition(body, bindings, definition);
                restore(bindings, name, previous);
                checked?;
            }
            ClickProposition::RangeAll {
                start,
                end,
                item,
                body,
                ..
            }
            | ClickProposition::RangeAny {
                start,
                end,
                item,
                body,
                ..
            } => {
                self.check_expression(start, bindings, definition)?;
                self.check_expression(end, bindings, definition)?;
                let previous = bindings.insert(item.clone(), None);
                let checked = self.check_proposition(body, bindings, definition);
                restore(bindings, item, previous);
                checked?;
            }
            // These query resources; their arguments cannot return a value
            // into the enclosing function's result or lexical bindings.
            ClickProposition::Separate { .. }
            | ClickProposition::Contains { .. }
            | ClickProposition::Loadable { .. } => {}
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests;
