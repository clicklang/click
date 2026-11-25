use super::*;
use crate::kernel::{KernelFold, KernelFoldIndex, KernelType};

#[derive(Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
pub(in crate::surface::proof) enum BinderCarrier {
    Program,
    Integer,
    Algebraic,
}

#[derive(Default)]
struct FoldNames {
    active: bool,
    // Integer and program variables are separate namespaces even at the same ID.
    names: BTreeMap<(BinderCarrier, Variable), SurfaceBinder>,
}

thread_local! {
    static FOLD_NAMES: std::cell::RefCell<FoldNames> = Default::default();
}

pub(in crate::surface::proof) fn binder_name(
    integer: bool,
    variable: Variable,
) -> Option<SurfaceBinder> {
    let carrier = if integer {
        BinderCarrier::Integer
    } else {
        BinderCarrier::Program
    };
    scoped_binder_name(carrier, variable)
}

pub(in crate::surface::proof) fn scoped_binder_name(
    carrier: BinderCarrier,
    variable: Variable,
) -> Option<SurfaceBinder> {
    FOLD_NAMES.with(|slot| slot.borrow().names.get(&(carrier, variable)).cloned())
}

/// Whether an enclosing binder of this raise is spelled `name`, so a new
/// binder of that name would shadow it. Bounded by the binder nesting.
pub(in crate::surface::proof) fn written_name_in_scope(name: &str) -> bool {
    FOLD_NAMES.with(|slot| {
        slot.borrow()
            .names
            .values()
            .any(|binder| binder.written() == Some(name))
    })
}

pub(in crate::surface::proof) fn marker(_preferred: Option<&str>) -> SurfaceBinder {
    SurfaceBinder::fresh()
}

pub(in crate::surface::proof) fn scope(
    f: impl FnOnce() -> Option<SyntaxTerm>,
) -> Option<SyntaxTerm> {
    let query = Query(FOLD_NAMES.with(|slot| {
        let mut names = slot.borrow_mut();
        let outermost = !names.active;
        names.active = true;
        outermost
    }));
    let _query = query;
    f()
}

struct Query(bool);
impl Drop for Query {
    fn drop(&mut self) {
        if self.0 {
            FOLD_NAMES.with(|slot| *slot.borrow_mut() = FoldNames::default());
        }
    }
}

pub(in crate::surface::proof) struct Binding {
    key: (BinderCarrier, Variable),
    previous: Option<SurfaceBinder>,
}
impl Binding {
    pub(in crate::surface::proof) fn enter(
        key: (BinderCarrier, Variable),
        name: SurfaceBinder,
    ) -> Self {
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

pub(in crate::surface::proof) fn raise_fold(
    fold: &KernelFold,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    raise_parts(
        fold.index,
        fold.result_type() == &KernelType::Integer,
        fold.accumulator,
        fold.item,
        fold.arguments.each_ref(),
        |term| raise_kernel_term(term, parameter_binding, state, bound_variables),
    )
}

pub(in crate::surface::proof) fn raise_machine_fold(
    term: &OldMachineTerm,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    let fold = KernelFold::import_machine(&mut crate::kernel::KernelTermImport::default(), term)?;
    raise_fold(&fold, parameter_binding, state, bound_variables)
}

fn raise_parts<T>(
    index: KernelFoldIndex,
    integer_result: bool,
    accumulator_id: Variable,
    item_id: Variable,
    arguments: [&T; 4],
    recurse: impl Fn(&T) -> Option<SyntaxTerm>,
) -> Option<SyntaxTerm> {
    scope(|| {
        let [start, end, initial, body] = arguments;
        let start = recurse(start)?;
        let end = recurse(end)?;
        let initial = recurse(initial)?;
        let initial = if integer_result {
            integer_typed_expression(initial)
        } else {
            initial
        };
        let accumulator = marker(None);
        let item = marker(None);
        let body = {
            let _acc = Binding::enter(
                (
                    if integer_result {
                        BinderCarrier::Integer
                    } else {
                        BinderCarrier::Program
                    },
                    accumulator_id,
                ),
                accumulator.clone(),
            );
            let _item = Binding::enter(
                (
                    if index == KernelFoldIndex::Integer {
                        BinderCarrier::Integer
                    } else {
                        BinderCarrier::Program
                    },
                    item_id,
                ),
                item.clone(),
            );
            recurse(body)?
        };
        let (start, end, bounds) = if index == KernelFoldIndex::Integer {
            let start_name = marker(None);
            let end_name = marker(None);
            (
                start_name.reference(),
                end_name.reference(),
                Some((start_name, start, end_name, end)),
            )
        } else {
            (start, end, None)
        };
        let expression = SyntaxTerm::RangeFold {
            start: Box::new(start),
            end: Box::new(end),
            initial: Box::new(initial),
            accumulator,
            item,
            body: Box::new(body),
        };
        let expression = if let Some((start_name, start, end_name, end)) = bounds {
            SyntaxTerm::Let {
                name: start_name,
                click_type: Some(ClickType::Integer),
                value: Box::new(start),
                body: Box::new(SyntaxTerm::Let {
                    name: end_name,
                    click_type: Some(ClickType::Integer),
                    value: Box::new(end),
                    body: Box::new(expression),
                }),
            }
        } else {
            expression
        };
        Some(expression)
    })
}
