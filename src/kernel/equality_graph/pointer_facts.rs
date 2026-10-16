//! Shared pointer-class lookup for predicate facts and callback witnesses.
//! Exact source handles are payloads, never class keys or inferred premises.
use super::*;

impl EqualityGraph {
    #[cfg(test)]
    pub(in crate::kernel) fn take_pointer_fact_merge_visits() -> usize {
        terms::take_pointer_fact_merge_visits()
    }

    pub(in crate::kernel) fn clear_pointer_predicates(&self) {
        let mut state = self.state.lock().expect("equality graph");
        state.pointer_predicate_inputs = Default::default();
        state.terms.clear_pointer_facts();
    }
    fn pointer_predicate_key(
        proposition: &crate::kernel::Proposition,
    ) -> Option<(Pointer, terms::PointerFactKey)> {
        use crate::kernel::{CValue, Proposition, Term};
        let Proposition::Predicate { name, arguments } = proposition else {
            return None;
        };
        let (position, pointer) =
            arguments
                .iter()
                .enumerate()
                .find_map(|(position, argument)| {
                    if let Term::CValue(CValue::Pointer(pointer)) = argument {
                        Some((position, pointer))
                    } else {
                        None
                    }
                })?;
        let key = crate::kernel::proof::fact_keys::pointer_predicate_selector(proposition)
            .map(terms::PointerFactKey::Predicate)
            .unwrap_or_else(|| {
                terms::PointerFactKey::PredicateShape(
                    name.clone(),
                    arguments.len(),
                    position,
                    pointer.c_type(),
                )
            });
        Some((pointer.pointer().clone(), key))
    }

    /// Retain an exact source proposition in the selected pointer's checked
    /// class. This adds no equality, read permission, or snapshot transport.
    pub(in crate::kernel) fn adjust_pointer_predicate(
        &self,
        source: &std::sync::Arc<crate::kernel::ExecutionPureFact>,
        insert: bool,
    ) {
        let source = source.clone() as std::sync::Arc<dyn terms::PointerFactSource>;
        self.adjust_pointer_predicate_source(&source, insert);
    }

    pub(super) fn adjust_pointer_predicate_source(
        &self,
        source: &std::sync::Arc<dyn terms::PointerFactSource>,
        insert: bool,
    ) {
        use crate::kernel::{CFunctionContract, CValue, Proposition, Term};
        let proposition = source.proposition();
        let Some((pointer, key)) = Self::pointer_predicate_key(proposition) else {
            return;
        };
        self.address_class(&pointer);
        let mut state = self.state.lock().expect("equality graph");
        let identity = std::sync::Arc::as_ptr(source) as *const () as usize;
        if insert {
            state
                .pointer_predicate_inputs
                .insert(identity, source.clone());
        } else {
            state.pointer_predicate_inputs.remove(&identity);
        }
        let address = state.register_pointer_address(&pointer);
        state
            .terms
            .adjust_pointer_fact(address, key, source, insert);
        // A contract fact names its function value first; the values after
        // it fix the contract's value parameters.
        if let Proposition::Predicate { name, arguments } = proposition
            && CFunctionContract::surface_name_from_predicate(name).is_some()
            && matches!(
                arguments.as_slice(),
                [Term::CState(_), Term::CValue(CValue::Pointer(_)), values @ ..]
                    if values.iter().all(|value| matches!(value, Term::CValue(_)))
            )
        {
            state.terms.adjust_pointer_fact(
                address,
                terms::PointerFactKey::FunctionContracts,
                source,
                insert,
            );
        }
    }

    fn pointer_fact_candidates(
        &self,
        pointer: &Pointer,
        key: &terms::PointerFactKey,
    ) -> terms::PointerFactBucket {
        let address = self
            .address_class(pointer)
            .expect("registered pointer address");
        self.state
            .lock()
            .expect("equality graph")
            .terms
            .pointer_facts(address, key)
    }

    pub(in crate::kernel) fn knows_pointer_predicate(
        &self,
        proposition: &crate::kernel::Proposition,
    ) -> bool {
        use crate::kernel::{CValue, Proposition, Term};
        let Some((pointer, key)) = Self::pointer_predicate_key(proposition) else {
            return false;
        };
        let Proposition::Predicate { name, arguments } = proposition else {
            return false;
        };
        self.pointer_fact_candidates(&pointer, &key)
            .get(&String::new())
            .cloned()
            .unwrap_or_default()
            .iter()
            .any(|(_, source)| {
                crate::instrumentation::record_deterministic_work(1);
                let Proposition::Predicate {
                    name: source_name,
                    arguments: source_arguments,
                } = source.proposition()
                else {
                    return false;
                };
                name == source_name
                    && arguments.len() == source_arguments.len()
                    && arguments.iter().zip(source_arguments).all(|(left, right)| {
                        crate::instrumentation::record_deterministic_work(1);
                        match (left, right) {
                            (
                                Term::CValue(CValue::Pointer(left)),
                                Term::CValue(CValue::Pointer(right)),
                            ) => {
                                left.c_type() == right.c_type()
                                    && left.pointee_volatile() == right.pointee_volatile()
                                    && self.are_equal(left.pointer(), right.pointer())
                            }
                            _ => left == right,
                        }
                    })
            })
    }

    /// Call consumers use the same class-bucket mechanism as predicates.
    /// The caller still checks the declared contract's exact call signature.
    /// A contract appears once for each distinct list of values its facts
    /// fix for its value parameters: once for a contract with none.
    pub(in crate::kernel) fn pointer_function_contracts(
        &self,
        pointer: &Pointer,
    ) -> impl Iterator<Item = (String, crate::kernel::Proposition)> {
        self.pointer_fact_candidates(pointer, &terms::PointerFactKey::FunctionContracts)
            .iter()
            .map(|(group, sources)| {
                crate::instrumentation::record_deterministic_work(1);
                let name = group
                    .split_once(terms::CONTRACT_VALUES_SEPARATOR)
                    .map_or(group.as_str(), |(name, _)| name);
                (
                    name.to_string(),
                    sources
                        .iter()
                        .next()
                        .expect("nonempty contract sources")
                        .1
                        .proposition()
                        .clone(),
                )
            })
            .collect::<Vec<_>>()
            .into_iter()
    }
}
