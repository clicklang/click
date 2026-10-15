//! Conservative domain effects over the lowered value operations. These are
//! scoped hypotheses until the containing function's ordinary proof succeeds.
//! No address equation is used to turn one pointer value into another.
use super::*;

type Domains = crate::persistent::PersistentMap<String, CPointerResultDomain>;

pub(crate) fn candidate(function: &CFunction) -> CPointerResultDomain {
    let mut locals = Domains::default();
    for (index, parameter) in function.parameters().iter().enumerate() {
        let effect = CPointerResultDomain::Argument(index);
        if parameter.c_type().is_pointer() {
            locals.insert(parameter.name().to_owned(), effect);
        } else if matches!(parameter.c_type(), CType::Int64 | CType::UInt64) {
            locals.insert(
                parameter.name().to_owned(),
                CPointerResultDomain::Integer(Box::new(effect)),
            );
        }
    }
    let mut returns = Vec::new();
    statements(
        function.body(),
        &mut locals,
        &mut returns,
        &mut Changes::default(),
    );
    let effect = join_returns(returns);
    fn loads_input(effect: &CPointerResultDomain) -> bool {
        match effect {
            CPointerResultDomain::Loaded { .. } => true,
            CPointerResultDomain::Integer(inner) => loads_input(inner),
            _ => false,
        }
    }
    fn writes_memory(body: &CStatement) -> bool {
        match body {
            CStatement::TypedStore { .. } => true,
            CStatement::Seq(left, right) => writes_memory(left) || writes_memory(right),
            CStatement::If {
                then_branch,
                else_branch,
                ..
            } => writes_memory(then_branch) || writes_memory(else_branch),
            _ => false,
        }
    }
    // An entry-load summary is not a hypothesis about a value read after a
    // store. Let the checked final value infer its actual origin instead.
    if loads_input(&effect) && writes_memory(function.body()) {
        CPointerResultDomain::Unknown
    } else {
        effect
    }
}

/// Compile all source return cases once. Per-call work depends on the
/// referenced arguments, not the number of return statements.
pub(crate) fn join_returns(effects: Vec<CPointerResultDomain>) -> CPointerResultDomain {
    let Some(first) = effects.first() else {
        return CPointerResultDomain::Unknown;
    };
    if effects.iter().all(|effect| effect == first) {
        return first.clone();
    }
    use num_traits::ToPrimitive;
    let mut lower = i64::MIN;
    let mut upper = i64::MAX;
    let mut fixed = false;
    let mut arguments = BTreeMap::<usize, (i64, i64)>::new();
    let mut selected_inputs = BTreeMap::<usize, (i64, i64)>::new();
    for effect in effects {
        match effect {
            CPointerResultDomain::Selected { domain, argument } => {
                let Some(position) = domain.position.as_const().and_then(ToPrimitive::to_i64)
                else {
                    return CPointerResultDomain::Unknown;
                };
                let Some(start) = position.checked_neg() else {
                    return CPointerResultDomain::Unknown;
                };
                let Some(end) = i64::from(domain.bytes).checked_sub(position) else {
                    return CPointerResultDomain::Unknown;
                };
                if let Some((index, offset)) = argument {
                    let Some(start) = offset.checked_sub(position) else {
                        return CPointerResultDomain::Unknown;
                    };
                    let Some(end) = start.checked_add(i64::from(domain.bytes)) else {
                        return CPointerResultDomain::Unknown;
                    };
                    let bounds = selected_inputs.entry(index).or_insert((start, end));
                    bounds.0 = bounds.0.min(start);
                    bounds.1 = bounds.1.max(end);
                }
                lower = lower.max(start);
                upper = upper.min(end);
                fixed = true;
            }
            CPointerResultDomain::Argument(index)
            | CPointerResultDomain::ArgumentOffset(index, 0) => {
                let bounds = arguments.entry(index).or_insert((0, 0));
                bounds.0 = bounds.0.min(0);
                bounds.1 = bounds.1.max(0);
            }
            CPointerResultDomain::ArgumentOffset(index, offset) => {
                let bounds = arguments.entry(index).or_insert((offset, offset));
                bounds.0 = bounds.0.min(offset);
                bounds.1 = bounds.1.max(offset);
            }
            _ => return CPointerResultDomain::Unknown,
        }
    }
    let fixed = if fixed {
        Some(if lower > upper {
            CPointerDomain {
                bytes: 0,
                position: IntegerTerm::constant_i64(0).into(),
            }
        } else {
            let Some(bytes) = upper
                .checked_sub(lower)
                .and_then(|bytes| u32::try_from(bytes).ok())
            else {
                return CPointerResultDomain::Unknown;
            };
            CPointerDomain {
                bytes,
                position: IntegerTerm::constant_i64(
                    lower.checked_neg().expect("bounded domain position"),
                )
                .into(),
            }
        })
    } else {
        None
    };
    CPointerResultDomain::Meet {
        fixed,
        arguments: arguments
            .into_iter()
            .map(|(index, (low, high))| (index, low, high))
            .collect(),
        selected_inputs: selected_inputs
            .into_iter()
            .map(|(index, (low, high))| (index, low, high))
            .collect(),
    }
}

pub(super) fn expression(value: &CExpression, locals: &Domains) -> CPointerResultDomain {
    use CExpression as E;
    match value {
        E::Value(CValue::Pointer(pointer)) => pointer
            .domain()
            .map(|domain| CPointerResultDomain::Selected {
                domain: domain.clone(),
                argument: None,
            })
            .unwrap_or(CPointerResultDomain::Unknown),
        E::Variable(name) => locals
            .get(name)
            .cloned()
            .unwrap_or(CPointerResultDomain::Unknown),
        E::Cast {
            expression: inner,
            target_type,
            ..
        } if target_type.is_pointer() => match expression(inner, locals) {
            CPointerResultDomain::Integer(origin) => *origin,
            value => value,
        },
        E::Cast {
            expression: inner,
            target_type: CType::Int64 | CType::UInt64,
            ..
        } => match expression(inner, locals) {
            effect @ CPointerResultDomain::Integer(_) => effect,
            CPointerResultDomain::Unknown => CPointerResultDomain::Unknown,
            effect => CPointerResultDomain::Integer(Box::new(effect)),
        },
        E::TypedLoad {
            pointer,
            value_type,
            volatile: false,
            ..
        } if value_type.is_object_pointer()
            || matches!(value_type, CType::Int64 | CType::UInt64) =>
        {
            let Some((argument, offset)) = argument(&expression(pointer, locals)) else {
                return CPointerResultDomain::Unknown;
            };
            let effect = CPointerResultDomain::Loaded {
                argument,
                offset,
                value_type: *value_type,
            };
            if value_type.is_pointer() {
                effect
            } else {
                CPointerResultDomain::Integer(Box::new(effect))
            }
        }
        E::AddressOf(place) | E::CheckedObjectAddress(place) => match place.as_ref() {
            E::Load(pointer) | E::TypedLoad { pointer, .. } => expression(pointer, locals),
            _ => CPointerResultDomain::Unknown,
        },
        E::Subobject { pointer, width } => {
            let parent = expression(pointer, locals);
            if parent == CPointerResultDomain::Unknown {
                return CPointerResultDomain::Unknown;
            }
            CPointerResultDomain::Selected {
                domain: CPointerDomain {
                    bytes: *width,
                    position: IntegerTerm::constant_i64(0).into(),
                },
                argument: argument(&parent),
            }
        }
        E::PointerOffsetBytes {
            pointer,
            bytes,
            object_bytes,
        } => {
            let parent = expression(pointer, locals);
            if parent == CPointerResultDomain::Unknown {
                return CPointerResultDomain::Unknown;
            }
            if let Some(bytes) = object_bytes {
                CPointerResultDomain::Selected {
                    domain: CPointerDomain {
                        bytes: *bytes,
                        position: IntegerTerm::constant_i64(0).into(),
                    },
                    argument: argument(&parent),
                }
            } else {
                displace(parent, i64::from(*bytes))
            }
        }
        E::BitwiseAnd(left, right) | E::BitwiseOr(left, right) | E::BitwiseXor(left, right) => {
            let left_effect = expression(left, locals);
            let right_effect = expression(right, locals);
            let (effect, other) = match (&left_effect, &right_effect) {
                (CPointerResultDomain::Integer(_), CPointerResultDomain::Unknown) => {
                    (left_effect, right)
                }
                (CPointerResultDomain::Unknown, CPointerResultDomain::Integer(_)) => {
                    (right_effect, left)
                }
                _ => return CPointerResultDomain::Unknown,
            };
            if matches!(value, E::BitwiseAnd(..))
                && constant_word(other).is_none_or(|mask| mask & (1u64 << 63) == 0)
            {
                CPointerResultDomain::Unknown
            } else {
                effect
            }
        }
        E::Add(left, right) | E::Subtract(left, right) => {
            let left_origin = expression(left, locals);
            let right_origin = expression(right, locals);
            if matches!(&left_origin, CPointerResultDomain::Integer(_))
                && right_origin == CPointerResultDomain::Unknown
            {
                return left_origin;
            }
            if matches!(value, E::Add(..))
                && matches!(&right_origin, CPointerResultDomain::Integer(_))
                && left_origin == CPointerResultDomain::Unknown
            {
                return right_origin;
            }
            // Typed pointer steps retain the operand's domain. The selected
            // domain's scalar type is recovered from the address expression.
            let E::Value(CValue::Int32(Bitvector32Term::Constant(index))) = right.as_ref() else {
                return CPointerResultDomain::Unknown;
            };
            if *index == 0 {
                return expression(left, locals);
            }
            let Some(width) = pointer_width(left) else {
                return CPointerResultDomain::Unknown;
            };
            let offset = i64::from(*index as i32) * i64::from(width);
            displace(
                expression(left, locals),
                if matches!(value, E::Subtract(..)) {
                    -offset
                } else {
                    offset
                },
            )
        }
        E::Conditional {
            then_branch,
            else_branch,
            ..
        } => {
            let left = expression(then_branch, locals);
            if left == expression(else_branch, locals) {
                left
            } else {
                CPointerResultDomain::Unknown
            }
        }
        _ => CPointerResultDomain::Unknown,
    }
}

fn constant_word(value: &CExpression) -> Option<u64> {
    match value {
        CExpression::Value(CValue::Int32(Bitvector32Term::Constant(value))) => {
            Some(*value as i32 as i64 as u64)
        }
        CExpression::Value(CValue::UInt32(Bitvector32Term::Constant(value))) => {
            Some(u64::from(*value))
        }
        CExpression::Value(CValue::Int64(value) | CValue::UInt64(value)) => {
            value.bitvector64_as_const()
        }
        CExpression::BitwiseNot(inner) => {
            let value = !constant_word(inner)?;
            Some(
                if matches!(inner.as_ref(), CExpression::Value(CValue::UInt32(_))) {
                    u64::from(value as u32)
                } else {
                    value
                },
            )
        }
        CExpression::Cast {
            expression,
            target_type: CType::Int64 | CType::UInt64,
            ..
        } => constant_word(expression),
        _ => None,
    }
}

fn pointer_width(value: &CExpression) -> Option<u32> {
    match value {
        CExpression::AddressOf(place) | CExpression::CheckedObjectAddress(place) => {
            match place.as_ref() {
                CExpression::TypedLoad { value_type, .. } => Some(value_type.byte_width()),
                _ => None,
            }
        }
        CExpression::Cast { target_type, .. } => target_type.pointee_type().map(CType::byte_width),
        CExpression::Value(CValue::Pointer(pointer)) => {
            pointer.c_type().pointee_type().map(CType::byte_width)
        }
        _ => None,
    }
}

pub(super) fn argument(value: &CPointerResultDomain) -> Option<(usize, i64)> {
    match value {
        CPointerResultDomain::Argument(index) => Some((*index, 0)),
        CPointerResultDomain::ArgumentOffset(index, offset) => Some((*index, *offset)),
        CPointerResultDomain::Selected { argument, .. } => *argument,
        _ => None,
    }
}
fn displace(value: CPointerResultDomain, bytes: i64) -> CPointerResultDomain {
    if bytes == 0 {
        return value;
    }
    match value {
        CPointerResultDomain::Selected { domain, argument } => CPointerResultDomain::Selected {
            domain: CPointerDomain {
                bytes: domain.bytes,
                position: IntegerTerm::add(
                    domain.position.as_ref().clone(),
                    IntegerTerm::constant_i64(bytes),
                )
                .into(),
            },
            argument: argument.and_then(|(index, offset)| {
                offset.checked_add(bytes).map(|offset| (index, offset))
            }),
        },
        CPointerResultDomain::Argument(index) => CPointerResultDomain::ArgumentOffset(index, bytes),
        CPointerResultDomain::ArgumentOffset(index, offset) => offset
            .checked_add(bytes)
            .map(|offset| CPointerResultDomain::ArgumentOffset(index, offset))
            .unwrap_or(CPointerResultDomain::Unknown),
        _ => CPointerResultDomain::Unknown,
    }
}

#[derive(Default)]
struct Changes {
    names: BTreeSet<String>,
    all: bool,
}
impl Changes {
    fn extend(&mut self, other: Self) {
        self.all |= other.all;
        self.names.extend(other.names);
    }
}

fn statements(
    body: &CStatement,
    locals: &mut Domains,
    returns: &mut Vec<CPointerResultDomain>,
    changed: &mut Changes,
) -> bool {
    crate::instrumentation::record_deterministic_work(1);
    match body {
        CStatement::Seq(left, right) => {
            statements(left, locals, returns, changed)
                && statements(right, locals, returns, changed)
        }
        CStatement::Declare {
            name, initializer, ..
        } => {
            let value = initializer
                .as_ref()
                .map(|value| expression(value, locals))
                .unwrap_or(CPointerResultDomain::Unknown);
            changed.names.insert(name.clone());
            locals.insert(name.clone(), value);
            true
        }
        CStatement::Assign {
            name,
            expression: value,
            ..
        } => {
            let value = expression(value, locals);
            changed.names.insert(name.clone());
            locals.insert(name.clone(), value);
            true
        }
        CStatement::HeapAllocate { target, bytes, .. } => {
            changed.names.insert(target.clone());
            let effect = constant_word(bytes)
                .and_then(|bytes| u32::try_from(bytes).ok())
                .map(|bytes| CPointerResultDomain::Selected {
                    domain: CPointerDomain {
                        bytes,
                        position: IntegerTerm::constant_i64(0).into(),
                    },
                    argument: None,
                })
                .unwrap_or(CPointerResultDomain::Unknown);
            locals.insert(target.clone(), effect);
            true
        }
        CStatement::CallAssign { target, .. } => {
            changed.names.insert(target.clone());
            locals.insert(target.clone(), CPointerResultDomain::Unknown);
            true
        }
        CStatement::TypedStore { pointer, .. }
            if expression(pointer, locals) != CPointerResultDomain::Unknown =>
        {
            // A write through an input/heap object cannot replace a scalar
            // local binding. Address-backed local destinations stay unknown.
            true
        }
        CStatement::Return(value) => {
            returns.push(expression(value, locals));
            false
        }
        CStatement::If {
            then_branch,
            else_branch,
            ..
        } => {
            let mut left = locals.clone();
            let mut right = locals.clone();
            let mut left_changes = Changes::default();
            let mut right_changes = Changes::default();
            let left_continues = statements(then_branch, &mut left, returns, &mut left_changes);
            let right_continues = statements(else_branch, &mut right, returns, &mut right_changes);
            if left_continues && right_continues {
                if left_changes.all || right_changes.all {
                    *locals = Domains::default();
                } else {
                    // Unchanged entries already share the parent map. Join
                    // only bindings written by these branches.
                    for name in left_changes.names.union(&right_changes.names) {
                        let value = left.get(name);
                        if value == right.get(name) {
                            if let Some(value) = value {
                                locals.insert(name.clone(), value.clone());
                            }
                        } else {
                            locals.remove(name);
                        }
                    }
                }
            } else if left_continues {
                *locals = left;
            } else if right_continues {
                *locals = right;
            }
            changed.extend(left_changes);
            changed.extend(right_changes);
            left_continues || right_continues
        }
        CStatement::Skip | CStatement::Assert { .. } | CStatement::EndAutomaticLifetimes { .. } => {
            true
        }
        // Memory writes may change a parameter whose address was taken.
        // Keep no value-origin assertion across an operation not modeled here.
        _ => {
            changed.all = true;
            *locals = Domains::default();
            returns.push(CPointerResultDomain::Unknown);
            true
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn return_domain_join_keeps_the_common_displacement_window() {
        let selected = |position| CPointerResultDomain::Selected {
            domain: CPointerDomain {
                bytes: 4,
                position: IntegerTerm::constant_i64(position).into(),
            },
            argument: None,
        };
        for count in [16, 64, 256, 1024] {
            let mut effects = vec![selected(4); count];
            effects.push(selected(0));
            let CPointerResultDomain::Meet {
                fixed: Some(domain),
                arguments,
                ..
            } = join_returns(effects)
            else {
                panic!("mixed scalar endpoints must retain their intersection");
            };
            assert_eq!(domain.bytes, 0);
            assert_eq!(
                domain.position.as_const(),
                IntegerTerm::constant_i64(0).as_const()
            );
            assert!(arguments.is_empty());
            let mut effects = vec![CPointerResultDomain::ArgumentOffset(0, 4); count];
            effects.push(CPointerResultDomain::Argument(0));
            assert!(matches!(join_returns(effects), CPointerResultDomain::Meet {
                fixed: None, arguments, ..
            } if arguments == vec![(0, 0, 4)]));
        }
    }

    #[test]
    fn branch_domain_join_touches_changed_bindings_only() {
        let mut costs = Vec::new();
        for count in [16, 64, 256, 1024] {
            let mut locals = Domains::default();
            for index in 0..count {
                locals.insert(
                    format!("unrelated{index}"),
                    CPointerResultDomain::Argument(index),
                );
            }
            locals.insert("selected".into(), CPointerResultDomain::Argument(0));
            let assign = CStatement::Assign {
                name: "selected".into(),
                expression: CExpression::Variable("selected".into()),
                source: Default::default(),
            };
            let branch = CStatement::If {
                condition: CExpression::Value(CValue::Int32(Bitvector32Term::Constant(1))),
                then_branch: Box::new(assign.clone()),
                else_branch: Box::new(assign),
            };
            let (_, work) = crate::persistent::measure_persistent_work(|| {
                assert!(statements(
                    &branch,
                    &mut locals,
                    &mut Vec::new(),
                    &mut Changes::default()
                ));
            });
            assert_eq!(
                locals.get("selected"),
                Some(&CPointerResultDomain::Argument(0))
            );
            assert_eq!(locals.len(), count + 1);
            costs.push(work);
        }
        assert!(costs[3] <= costs[0] * 4 + 32, "{costs:?}");
    }
}
