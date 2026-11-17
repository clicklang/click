//! Producer-retained lexical names for proof-local variables. Updating a
//! scope visits its persistent-map delta; spelling a selected variable reads
//! one index entry, without enumerating the proof's other bindings.
use super::*;

#[derive(Clone, Default)]
pub(in crate::surface::proof) struct BindingNames {
    names: PersistentMap<Variable, PersistentBinderMap<u8>>,
}

pub(in crate::surface::proof) fn variable(expression: &ContractExpression) -> Option<Variable> {
    match expression {
        ContractExpression::ProgramExpression(ProgramExpression::Value(ProgramValue::Pointer(
            pointer,
        ))) => match (&pointer.pointer().block, &pointer.pointer().offset) {
            (crate::kernel::PointerBlock::Symbolic(variable), PointerOffsetTerm::Constant(0)) => {
                Some(*variable)
            }
            _ => None,
        },
        ContractExpression::ProgramExpression(ProgramExpression::Value(value)) => {
            diagnostic_value_variable(value)
        }
        ContractExpression::AlgebraicVariable { binder_index, .. } => {
            crate::surface::lowering::algebraic_binder_variable(*binder_index).ok()
        }
        _ => None,
    }
}

impl BindingNames {
    pub(super) fn update_values(
        &mut self,
        before: &PersistentBinderMap<ContractExpression>,
        after: &PersistentBinderMap<ContractExpression>,
    ) {
        self.update(before, after, 1, variable);
    }

    pub(super) fn update_integers(
        &mut self,
        before: &PersistentBinderMap<crate::kernel::SpecIntegerExpression>,
        after: &PersistentBinderMap<crate::kernel::SpecIntegerExpression>,
    ) {
        self.update(before, after, 2, |expression| match expression {
            crate::kernel::SpecIntegerExpression::Term(crate::kernel::IntegerTerm::Variable(
                variable,
            )) => Some(*variable),
            _ => None,
        });
    }

    pub(super) fn update_algebraics(
        &mut self,
        before: &PersistentBinderMap<crate::kernel::SpecAlgebraicExpression>,
        after: &PersistentBinderMap<crate::kernel::SpecAlgebraicExpression>,
    ) {
        self.update(before, after, 4, |expression| match expression.node {
            crate::kernel::SpecAlgebraicExpressionNode::Variable(variable) => Some(variable),
            _ => None,
        });
    }

    fn update<T: PartialEq + Clone>(
        &mut self,
        before: &PersistentBinderMap<T>,
        after: &PersistentBinderMap<T>,
        kind: u8,
        variable: impl Fn(&T) -> Option<Variable>,
    ) {
        for (name, before, after) in before.diff(after) {
            crate::instrumentation::record_deterministic_work(1);
            if let Some(variable) = before.and_then(&variable) {
                let names = self.names.get(&variable).expect("indexed proof binding");
                let kinds = *names.get(name).expect("indexed proof binding name") & !kind;
                let names = if kinds == 0 {
                    names.without_key(name)
                } else {
                    names.with_inserted(name.clone(), kinds)
                };
                if names.is_empty() {
                    self.names.remove(&variable);
                } else {
                    self.names.insert(variable, names);
                }
            }
            if let Some(variable) = after.and_then(&variable) {
                let names = self.names.get(&variable).cloned().unwrap_or_default();
                // The same lexical binder can be retained in its generic and
                // typed environments. Removing one must keep the other.
                let kinds = names.get(name).copied().unwrap_or(0) | kind;
                self.names
                    .insert(variable, names.with_inserted(name.clone(), kinds));
            }
        }
    }

    pub(in crate::surface::proof) fn name(&self, variable: Variable) -> Option<&SurfaceBinder> {
        crate::instrumentation::record_deterministic_work(1);
        self.names.get(&variable)?.keys().next()
    }
}
