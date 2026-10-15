//! Full pointer-cell equations inferred from straight-line source writes and
//! authenticated against every checked normal exit. Numeric postconditions do
//! not supply these equations.
use super::*;

pub(crate) fn candidates(function: &CFunction) -> Vec<CPointerStoreEffect> {
    struct Scan {
        locals: crate::persistent::PersistentMap<String, CPointerResultDomain>,
        root: Option<usize>,
        stores: BTreeMap<i64, CPointerStoreEffect>,
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
    };
    for (index, parameter) in function.parameters().iter().enumerate() {
        if parameter.c_type().is_pointer() {
            scan.locals.insert(
                parameter.name().into(),
                CPointerResultDomain::Argument(index),
            );
        }
    }
    if walk(function.body(), &mut scan).is_none() {
        return Vec::new();
    }
    scan.stores.into_values().collect()
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

pub(crate) fn value(effect: &CPointerStoreEffect, arguments: &[CValue]) -> Option<CValue> {
    Some(CValue::Pointer(
        instantiate_result_pointer_origin(&effect.value, arguments)?.with_type(effect.value_type),
    ))
}

pub(super) fn apply(
    state: &CState,
    arguments: &[CValue],
    effects: &[CPointerStoreEffect],
    assumptions: &PureFactContext,
) -> Option<CMemory> {
    let mut memory = state.memory().clone();
    for effect in effects {
        let destination = destination(effect, arguments)?;
        let value = value(effect, arguments)?;
        memory = memory.with_certified_pointer_cell(destination, value, assumptions)?;
    }
    Some(memory)
}
