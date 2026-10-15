//! Full pointer-cell equations inferred from straight-line source writes and
//! authenticated against every checked normal exit. Numeric postconditions do
//! not supply these equations.
use super::*;

pub(crate) fn candidates(function: &CFunction) -> Vec<CPointerStoreEffect> {
    struct Scan {
        locals: crate::persistent::PersistentMap<String, CPointerResultDomain>,
        root: Option<usize>,
        stores: BTreeMap<i64, CPointerStoreEffect>,
        wrote_memory: bool,
    }
    fn walk(body: &CStatement, scan: &mut Scan) -> Option<bool> {
        crate::instrumentation::record_deterministic_work(1);
        match body {
            CStatement::Seq(left, right) => {
                if !walk(left, scan)? {
                    return Some(false);
                }
                walk(right, scan)
            }
            CStatement::Declare {
                name, initializer, ..
            } => {
                let effect = initializer
                    .as_ref()
                    .map(|value| pointer_domain_inference::expression(value, &scan.locals))
                    .unwrap_or(CPointerResultDomain::Unknown);
                scan.locals.insert(name.clone(), effect);
                Some(true)
            }
            CStatement::Assign {
                name, expression, ..
            } => {
                let effect = pointer_domain_inference::expression(expression, &scan.locals);
                scan.locals.insert(name.clone(), effect);
                Some(true)
            }
            CStatement::TypedStore {
                pointer,
                value,
                value_type,
                volatile,
                ..
            } => {
                scan.wrote_memory = true;
                if *volatile {
                    return None;
                }
                let destination = pointer_domain_inference::expression(pointer, &scan.locals);
                let (root, offset) = pointer_domain_inference::argument(&destination)?;
                if scan.root != Some(root) {
                    // Distinct parameters may alias. Only the last root's
                    // final writes survive without a separate alias analysis.
                    scan.stores.clear();
                    scan.root = Some(root);
                }
                let end = offset.checked_add(i64::from(value_type.byte_width()))?;
                // All retained cells have width eight. Inspect only stores
                // overlapping this write, including partial overwrites.
                let overlaps = scan
                    .stores
                    .range(offset.saturating_sub(7)..end)
                    .map(|(offset, _)| *offset)
                    .collect::<Vec<_>>();
                for offset in overlaps {
                    scan.stores.remove(&offset);
                }
                if value_type.is_object_pointer() {
                    let effect = pointer_domain_inference::expression(value, &scan.locals);
                    if effect != CPointerResultDomain::Unknown {
                        scan.stores.insert(
                            offset,
                            CPointerStoreEffect {
                                destination: root,
                                offset,
                                value_type: *value_type,
                                value: effect,
                            },
                        );
                    }
                }
                Some(true)
            }
            CStatement::Return(_) => Some(false),
            CStatement::Skip
            | CStatement::Assert { .. }
            | CStatement::EndAutomaticLifetimes { .. } => Some(true),
            // Unsupported control flow never publishes a partial write set.
            _ => None,
        }
    }
    let mut scan = Scan {
        locals: Default::default(),
        root: None,
        stores: BTreeMap::new(),
        wrote_memory: false,
    };
    for (index, parameter) in function.parameters().iter().enumerate() {
        if parameter.c_type().is_pointer() {
            scan.locals.insert(
                parameter.name().into(),
                CPointerResultDomain::Argument(index),
            );
        }
    }
    let entry_locals = scan.locals.clone();
    if walk(function.body(), &mut scan).is_none() {
        return Vec::new();
    }
    let mut effects: Vec<_> = scan.stores.into_values().collect();
    if !scan.wrote_memory {
        fn spec_address(
            expression: &SpecExpression,
            locals: &crate::persistent::PersistentMap<String, CPointerResultDomain>,
        ) -> Option<(usize, i64)> {
            match expression {
                SpecExpression::CExpression(expression) => pointer_domain_inference::argument(
                    &pointer_domain_inference::expression(expression, locals),
                ),
                SpecExpression::PointerOffset {
                    pointer,
                    elements,
                    byte_width,
                    ..
                } => {
                    let (argument, offset) = spec_address(pointer, locals)?;
                    let (SpecExpression::Value(CValue::Int32(Bitvector32Term::Constant(index)))
                    | SpecExpression::CExpression(CExpression::Value(CValue::Int32(
                        Bitvector32Term::Constant(index),
                    )))) = elements.as_ref()
                    else {
                        return None;
                    };
                    Some((
                        argument,
                        offset.checked_add(
                            i64::from(*index as i32).checked_mul(i64::from(*byte_width))?,
                        )?,
                    ))
                }
                _ => None,
            }
        }
        let mut pointer_cells = BTreeMap::new();
        for ensure in function.contract_ensures() {
            let SpecProposition::Comparison { left, right, .. } = ensure else {
                continue;
            };
            for expression in [left, right] {
                let read = match expression {
                    SpecExpression::CExpression(CExpression::TypedLoad {
                        pointer,
                        value_type,
                        ..
                    }) => pointer_domain_inference::argument(
                        &pointer_domain_inference::expression(pointer, &entry_locals),
                    )
                    .map(|address| (address, *value_type)),
                    SpecExpression::MemoryLoad {
                        pointer,
                        value_type,
                        ..
                    } => spec_address(pointer, &entry_locals).map(|address| (address, *value_type)),
                    _ => None,
                };
                if let Some((address, value_type)) =
                    read.filter(|(_, value_type)| value_type.is_object_pointer())
                {
                    pointer_cells.insert(address, value_type);
                }
            }
        }
        fn cell_type(
            expression: &CExpression,
            function: &CFunction,
            locals: &crate::persistent::PersistentMap<String, CPointerResultDomain>,
        ) -> Option<CType> {
            match expression {
                CExpression::AddressOf(place) => match place.as_ref() {
                    CExpression::TypedLoad { value_type, .. } => Some(*value_type),
                    _ => None,
                },
                CExpression::Variable(name) => {
                    let CPointerResultDomain::Argument(index) = locals.get(name)? else {
                        return None;
                    };
                    function.parameters().get(*index)?.c_type().pointee_type()
                }
                CExpression::Subobject { pointer, .. }
                | CExpression::PointerOffsetBytes { pointer, .. } => {
                    cell_type(pointer, function, locals)
                }
                _ => None,
            }
        }
        for (&(argument, offset), &value_type) in &pointer_cells {
            effects.push(CPointerStoreEffect {
                destination: argument,
                offset,
                value_type,
                value: CPointerResultDomain::Loaded {
                    argument,
                    offset,
                    value_type,
                },
            });
        }
        for requirement in function.contract_interface().resource_requires() {
            let CResourceTerm::Memory(segment) = requirement.term() else {
                continue;
            };
            if requirement.guard().is_some()
                || segment.guard.is_some()
                || !matches!(
                    &segment.start,
                    CExpression::Value(CValue::Int32(Bitvector32Term::Constant(0)))
                )
                || !matches!(
                    &segment.end,
                    CExpression::Value(CValue::Int32(Bitvector32Term::Constant(end)))
                        if end.checked_mul(segment.element_width) == Some(8)
                )
            {
                continue;
            }
            let Some((argument, offset)) = pointer_domain_inference::argument(
                &pointer_domain_inference::expression(&segment.base, &entry_locals),
            ) else {
                continue;
            };
            let Some(value_type) = cell_type(&segment.base, function, &entry_locals)
                .filter(|ty| ty.is_object_pointer())
                .or_else(|| pointer_cells.get(&(argument, offset)).copied())
            else {
                continue;
            };
            if pointer_cells.contains_key(&(argument, offset)) {
                continue;
            }
            effects.push(CPointerStoreEffect {
                destination: argument,
                offset,
                value_type,
                value: CPointerResultDomain::Loaded {
                    argument,
                    offset,
                    value_type,
                },
            });
        }
    }
    effects
}

pub(crate) fn destination(effect: &CPointerStoreEffect, arguments: &[CValue]) -> Option<Pointer> {
    let CValue::Pointer(base) = arguments.get(effect.destination)? else {
        return None;
    };
    Some(Pointer {
        block: base.block.clone(),
        offset: PointerOffsetTerm::add(
            base.offset.clone(),
            PointerOffsetTerm::Constant(effect.offset),
        ),
    })
}

pub(crate) fn value(
    effect: &CPointerStoreEffect,
    state: &CState,
    arguments: &[CValue],
    assumptions: &PureFactContext,
) -> Option<CValue> {
    Some(CValue::Pointer(
        instantiate_result_pointer_geometry(&effect.value, state, arguments, assumptions)?
            .with_type(effect.value_type),
    ))
}

pub(super) fn apply(
    state: &CState,
    entry_state: &CState,
    arguments: &[CValue],
    effects: &[CPointerStoreEffect],
    assumptions: &PureFactContext,
) -> Option<CMemory> {
    let mut memory = state.memory().clone();
    for effect in effects {
        let destination = destination(effect, arguments)?;
        let value = value(effect, entry_state, arguments, assumptions)?;
        memory = memory.with_certified_pointer_cell(destination, value, assumptions)?;
    }
    Some(memory)
}
