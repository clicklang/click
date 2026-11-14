use super::*;
use crate::kernel::{KernelFold, KernelFoldIndex, KernelType};

#[derive(Default)]
struct FoldNames {
    active: bool,
    // Integer and C variables are separate namespaces even at the same ID.
    names: BTreeMap<(bool, Variable), String>,
    markers: Vec<String>,
}

thread_local! {
    static FOLD_NAMES: std::cell::RefCell<FoldNames> = Default::default();
}

pub(super) fn binder_name(integer: bool, variable: Variable) -> Option<String> {
    FOLD_NAMES.with(|slot| slot.borrow().names.get(&(integer, variable)).cloned())
}

struct Query(bool);
impl Drop for Query {
    fn drop(&mut self) {
        if self.0 {
            FOLD_NAMES.with(|slot| *slot.borrow_mut() = FoldNames::default());
        }
    }
}

struct Binding {
    key: (bool, Variable),
    previous: Option<String>,
}
impl Binding {
    fn enter(key: (bool, Variable), name: String) -> Self {
        let previous = FOLD_NAMES.with(|slot| slot.borrow_mut().names.insert(key, name));
        Self { key, previous }
    }
}
impl Drop for Binding {
    fn drop(&mut self) {
        FOLD_NAMES.with(|slot| {
            let mut names = slot.borrow_mut();
            if let Some(previous) = self.previous.take() {
                names.names.insert(self.key, previous);
            } else {
                names.names.remove(&self.key);
            }
        });
    }
}

pub(super) fn raise_fold(
    fold: &KernelFold,
    parameter_binding: ParameterBinding<'_>,
    state: &CState,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<SurfaceTerm> {
    raise_parts(
        fold.index,
        fold.result_type() == &KernelType::Integer,
        fold.accumulator,
        fold.item,
        fold.arguments.each_ref(),
        |term| raise_kernel_term(term, parameter_binding, state, bound_variables),
    )
}

pub(super) fn raise_machine_fold(
    term: &MachineTerm,
    parameter_binding: ParameterBinding<'_>,
    state: &CState,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<SurfaceTerm> {
    let MachineTerm::RangeFold {
        start,
        end,
        initial,
        accumulator,
        item,
        body,
    } = term
    else {
        return None;
    };
    raise_parts(
        KernelFoldIndex::Int32,
        false,
        *accumulator,
        *item,
        [
            start.as_ref(),
            end.as_ref(),
            initial.as_ref(),
            body.as_ref(),
        ],
        |term| synthesize_surface_bitvector(term, parameter_binding, state, bound_variables),
    )
}

fn raise_parts<T>(
    index: KernelFoldIndex,
    integer_result: bool,
    accumulator_id: Variable,
    item_id: Variable,
    arguments: [&T; 4],
    recurse: impl Fn(&T) -> Option<SurfaceTerm>,
) -> Option<SurfaceTerm> {
    let query = Query(FOLD_NAMES.with(|slot| {
        let mut names = slot.borrow_mut();
        let outermost = !names.active;
        names.active = true;
        outermost
    }));
    let [start, end, initial, body] = arguments;
    let start = recurse(start)?;
    let end = recurse(end)?;
    let initial = recurse(initial)?;
    let initial = if integer_result {
        integer_typed_expression(initial)
    } else {
        initial
    };
    let marker = || {
        FOLD_NAMES.with(|slot| {
            let mut names = slot.borrow_mut();
            // Never exposed to parsing or printing: finalized once at query exit.
            let marker = format!("\0fold{}", names.markers.len());
            names.markers.push(marker.clone());
            marker
        })
    };
    let accumulator = marker();
    let item = marker();
    let body = {
        let _acc = Binding::enter((integer_result, accumulator_id), accumulator.clone());
        let _item = Binding::enter((index == KernelFoldIndex::Integer, item_id), item.clone());
        recurse(body)?
    };
    let (start, end, bounds) = if index == KernelFoldIndex::Integer {
        let start_name = marker();
        let end_name = marker();
        (
            SurfaceTerm::Binding(start_name.clone()),
            SurfaceTerm::Binding(end_name.clone()),
            Some((start_name, start, end_name, end)),
        )
    } else {
        (start, end, None)
    };
    let expression = SurfaceTerm::RangeFold {
        start: Box::new(start),
        end: Box::new(end),
        initial: Box::new(initial),
        accumulator,
        item,
        body: Box::new(body),
    };
    let expression = if let Some((start_name, start, end_name, end)) = bounds {
        SurfaceTerm::Let {
            name: start_name,
            click_type: Some(ClickType::Integer),
            value: Box::new(start),
            body: Box::new(SurfaceTerm::Let {
                name: end_name,
                click_type: Some(ClickType::Integer),
                value: Box::new(end),
                body: Box::new(expression),
            }),
        }
    } else {
        expression
    };
    if query.0 {
        FOLD_NAMES.with(|slot| {
            crate::surface::lowering::name_synthesized_fold_binders(
                &expression,
                &slot.borrow().markers,
            )
            .ok()
        })
    } else {
        Some(expression)
    }
}
