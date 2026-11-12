//! Scoped alpha identities for selected native match leaves. Common parents
//! keep their DAG; only the existing match payload is visited here.
use super::*;
use crate::kernel::proof::term_rewrite::{BindingCarrier, binding_variable};

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub(super) struct Arm {
    variant: String,
    types: Vec<crate::kernel::AlgebraicValueType>,
    body: AlphaBitvectorKey,
}

pub(super) fn machine<const ALLOW_LOADS: bool>(
    scrutinee: &AlgebraicTerm,
    arms: &[crate::kernel::AlgebraicBitvectorMatchArm],
    bindings: &mut AlphaBindings,
    next_binder: &mut usize,
) -> Option<AlphaBitvectorKey> {
    let scrutinee =
        alpha_algebraic_key_with_bindings::<ALLOW_LOADS>(scrutinee, bindings, next_binder)?;
    let mut keys = Vec::with_capacity(arms.len());
    for arm in arms {
        alpha_work_checkpoint(bindings, 1)?;
        let outer_next = *next_binder;
        let outer_scopes = (bindings.integer_scope, bindings.bitvector_scope);
        let scope = bindings.next_scope_id;
        bindings.next_scope_id = scope.checked_add(1)?;
        bindings.integer_scope = scope;
        bindings.bitvector_scope = scope;
        let mut changes = Vec::with_capacity(arm.bindings.len());
        let result = (|| {
            let mut types = Vec::with_capacity(arm.bindings.len());
            for binding in &arm.bindings {
                alpha_work_checkpoint(bindings, 1)?;
                let (carrier, variable) = binding_variable(binding)?;
                let ordinal = *next_binder;
                *next_binder = ordinal.checked_add(1)?;
                let map = match carrier {
                    BindingCarrier::C => &mut bindings.bitvector,
                    BindingCarrier::Integer => &mut bindings.integer,
                    BindingCarrier::Algebraic => &mut bindings.algebraic,
                };
                changes.push((carrier, variable, map.insert(variable, ordinal)));
                types.push(binding.value_type());
            }
            let body =
                alpha_bitvector_key_with_bindings::<ALLOW_LOADS>(&arm.body, bindings, next_binder)?;
            Some(Arm {
                variant: arm.variant.clone(),
                types,
                body,
            })
        })();
        for (carrier, variable, prior) in changes.into_iter().rev() {
            let map = match carrier {
                BindingCarrier::C => &mut bindings.bitvector,
                BindingCarrier::Integer => &mut bindings.integer,
                BindingCarrier::Algebraic => &mut bindings.algebraic,
            };
            if let Some(prior) = prior {
                map.insert(variable, prior);
            } else {
                map.remove(&variable);
            }
        }
        (bindings.integer_scope, bindings.bitvector_scope) = outer_scopes;
        *next_binder = outer_next;
        keys.push(result?);
    }
    Some(AlphaBitvectorKey::AlgebraicMatch(Box::new(scrutinee), keys))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{AlgebraicBitvectorMatchArm, AlgebraicValue, CValue};

    fn selected_match(bound: u64, count: usize) -> MachineTerm {
        MachineTerm::AlgebraicMatch {
            scrutinee: Box::new(AlgebraicTerm {
                algebraic_type: crate::kernel::AlgebraicType::parameter("Payload".into()),
                node: AlgebraicTermNode::Variable(Variable(900)),
            }),
            arms: (0..count)
                .map(|index| AlgebraicBitvectorMatchArm {
                    variant: format!("Arm{index}"),
                    bindings: vec![AlgebraicValue::C(CValue::Int32(MachineTerm::Variable(
                        Variable(bound),
                    )))],
                    body: MachineTerm::Variable(Variable(bound)),
                    binding_names: Default::default(),
                })
                .collect(),
        }
    }

    fn key(term: &MachineTerm) -> Option<AlphaBitvectorKey> {
        alpha_bitvector_key::<false>(term, &mut BTreeMap::new(), &mut 0)
    }

    #[test]
    fn match_alpha_keys_preserve_free_variables_and_arm_scope() {
        let left = selected_match(100, 2);
        let right = selected_match(200, 2);
        assert!(key(&left).is_some());
        assert_eq!(key(&left), key(&right));
        let mut different = right.clone();
        let MachineTerm::AlgebraicMatch { arms, .. } = &mut different else {
            unreachable!()
        };
        arms[1].body = MachineTerm::Variable(Variable(100));
        assert_ne!(key(&left), key(&different));

        // A C binder must not capture an algebraic argument with the same ID.
        let with_free_algebraic = |bound| {
            let mut term = selected_match(bound, 1);
            let MachineTerm::AlgebraicMatch { arms, .. } = &mut term else {
                unreachable!()
            };
            arms[0].body = MachineTerm::ClickFunctionApplication {
                name: "read".into(),
                arguments: vec![PureFunctionArgument::Algebraic(AlgebraicTerm {
                    algebraic_type: crate::kernel::AlgebraicType::parameter("Other".into()),
                    node: AlgebraicTermNode::Variable(Variable(bound)),
                })],
            };
            term
        };
        assert_ne!(
            key(&with_free_algebraic(100)),
            key(&with_free_algebraic(200))
        );
    }

    mod scaling_tests {
        include!("../../../scaling_tests/kernel/proof/fact_keys/match_keys.rs");
    }
}
