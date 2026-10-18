//! Object-type requirements belong to declarations. Pointer origins only
//! transfer existing evidence through checked return summaries and words.
use super::effective_type;
use super::prelude::*;
use std::sync::Arc;

pub(super) fn nominal_class(class: &effective_type::CAccessClass) -> bool {
    use effective_type::{CAccessClass, CPointeeBase};
    matches!(
        class,
        CAccessClass::Struct(_)
            | CAccessClass::Pointer {
                base: CPointeeBase::Struct(_),
                ..
            }
    )
}

/// An explicit domain receipt from a checked logical call. Its typed value
/// is indexed like other admitted pointer evidence; opaque application nodes
/// supply no evidence. The class is visible in the ordinary fact printer.
pub(super) fn checked_call_type_fact(
    value: &CValue,
    class: &effective_type::CAccessClass,
) -> Proposition {
    Proposition::Predicate {
        name: format!("object_type[{class}]"),
        arguments: vec![Term::CValue(value.clone())],
    }
}

fn origin_fingerprint(scope: u64, parameter: usize) -> u64 {
    let mut hash = std::collections::hash_map::DefaultHasher::new();
    std::hash::Hash::hash(&(scope, parameter), &mut hash);
    std::hash::Hasher::finish(&hash)
}

impl ObjectTypeEvidence {
    pub(super) fn parameter(
        class: effective_type::CAccessClass,
        parameter: usize,
        scope: u64,
        checked: bool,
    ) -> Self {
        let premise = Arc::new(ObjectTypePremise {
            parameter,
            class: class.clone(),
            scope,
        });
        Self {
            class,
            checked,
            premise_fingerprint: origin_fingerprint(scope, parameter),
            premises: imbl::OrdMap::unit((scope, parameter), premise),
        }
    }

    pub(super) fn has_class(&self, class: &effective_type::CAccessClass) -> bool {
        self.checked && &self.class == class
    }

    pub(super) fn merge(mut self, other: &Self) -> Self {
        debug_assert_eq!(self.class, other.class);
        self.checked &= other.checked;
        for (index, premise) in &other.premises {
            crate::instrumentation::record_deterministic_work(1);
            if !self.premises.contains_key(index) {
                self.premise_fingerprint ^= origin_fingerprint(index.0, index.1);
                self.premises.insert(*index, premise.clone());
            }
        }
        self
    }
}

impl From<effective_type::CAccessClass> for ObjectTypeEvidence {
    fn from(class: effective_type::CAccessClass) -> Self {
        Self {
            class,
            checked: true,
            premise_fingerprint: 0,
            premises: Default::default(),
        }
    }
}

impl PartialEq for ObjectTypeEvidence {
    fn eq(&self, other: &Self) -> bool {
        self.class == other.class
            && self.checked == other.checked
            && self.premise_fingerprint == other.premise_fingerprint
            && self.premises == other.premises
    }
}
impl Eq for ObjectTypeEvidence {}
impl PartialOrd for ObjectTypeEvidence {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for ObjectTypeEvidence {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.class
            .cmp(&other.class)
            .then_with(|| self.checked.cmp(&other.checked))
            .then_with(|| self.premise_fingerprint.cmp(&other.premise_fingerprint))
            .then_with(|| {
                if self.premises.ptr_eq(&other.premises) {
                    std::cmp::Ordering::Equal
                } else {
                    self.premises.cmp(&other.premises)
                }
            })
    }
}
impl std::hash::Hash for ObjectTypeEvidence {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.class.hash(state);
        self.checked.hash(state);
        self.premise_fingerprint.hash(state);
    }
}

pub(super) fn merge_pointer_results<'a>(
    results: impl Iterator<Item = Option<&'a PurePointerResult>>,
) -> Option<Arc<PurePointerResult>> {
    let mut merged = PurePointerResult {
        classes: BTreeSet::new(),
        arguments: BTreeSet::new(),
    };
    let mut seen = std::collections::HashSet::new();
    for result in results {
        let result = result?;
        if !seen.insert(result as *const PurePointerResult) {
            continue;
        }
        merged.classes.extend(result.classes.iter().cloned());
        merged.arguments.extend(&result.arguments);
    }
    Some(Arc::new(merged))
}

pub(super) fn execution_pointer_result(
    cases: &[Vec<CContractPathSet>],
) -> Option<Arc<PurePointerResult>> {
    let mut result = PurePointerResult {
        classes: BTreeSet::new(),
        arguments: BTreeSet::new(),
    };
    for path in cases.iter().flatten().flat_map(|set| &set.paths) {
        let CFunctionOutcome::Return {
            value: CValue::Pointer(pointer),
            state,
        } = super::api::path_function_outcome(path)?
        else {
            continue;
        };
        if pointer.is_null() {
            continue;
        }
        let evidence = pointer.object_origin_evidence().cloned().or_else(|| {
            (pointer.offset == PointerOffsetTerm::Constant(0))
                .then(|| {
                    state
                        .memory()
                        .declared_class(pointer.pointer())
                        .map(ObjectTypeEvidence::from)
                })
                .flatten()
        })?;
        if evidence.premises.is_empty() {
            if !evidence.checked {
                return None;
            }
            result.classes.insert(evidence.class.clone());
        } else {
            result
                .arguments
                .extend(evidence.premises.values().map(|premise| premise.parameter));
        }
    }
    Some(Arc::new(result))
}

pub(super) fn check_requirements(
    name: &str,
    parameters: &[CParameter],
    requirements: &ObjectTypeRequirements,
    values: &mut [CValue],
    memory: &CMemory,
    assumptions: &PureFactContext,
) -> Option<CRuntimeError> {
    check_requirement_slice(
        name,
        parameters,
        requirements,
        values,
        memory,
        assumptions,
        0,
    )
}

pub(super) fn check_value_requirements(
    name: &str,
    interface: &CFunctionContractInterface,
    values: &mut [CValue],
    memory: &CMemory,
    assumptions: &PureFactContext,
) -> Option<CRuntimeError> {
    check_requirement_slice(
        name,
        interface.value_parameters(),
        interface.object_type_requirements(),
        values,
        memory,
        assumptions,
        interface.parameters().len(),
    )
}

fn check_requirement_slice(
    name: &str,
    parameters: &[CParameter],
    requirements: &ObjectTypeRequirements,
    values: &mut [CValue],
    memory: &CMemory,
    assumptions: &PureFactContext,
    offset: usize,
) -> Option<CRuntimeError> {
    requirements
        .range(offset..offset + parameters.len())
        .find_map(|(index, class)| {
            crate::instrumentation::record_deterministic_work(1);
            let local = index - offset;
            let Some(value) = values.get_mut(local) else {
                return Some(CRuntimeError::FunctionContract(format!(
                    "call to `{name}` lacks value for typed parameter `{}`",
                    parameters[local].name()
                )));
            };
            (!refine_object_pointer_argument(value, class, memory, assumptions)).then(|| {
            CRuntimeError::FunctionContract(format!(
                "call to `{name}` parameter `{}` requires original object class `{class}` or null",
                parameters[local].name()
            ))
        })
        })
}

mod contract_requirements;
pub(super) use contract_requirements::{declared_requirements, declared_return_class};

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::effective_type::{CAccessClass, CStructClass};
    fn class() -> CAccessClass {
        CAccessClass::Struct(CStructClass::opaque("node"))
    }
    #[test]
    fn declared_designations_supply_type_evidence_without_changing_pointer_views() {
        let object = Pointer {
            block: "declared_node".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let memory = CMemory::new().with_classed_block(object.block.clone(), Some(class()), 8);
        let make = |designation| {
            let CValue::Pointer(pointer) =
                CValue::typed_pointer(Pointer::symbolic(Variable(900_010)), CType::Int32Pointer)
            else {
                unreachable!()
            };
            CValue::Pointer(pointer.with_designation(Arc::new(designation)))
        };
        let original = make(object.clone());
        let mut refined = original.clone();
        assert!(refine_object_pointer_argument(
            &mut refined,
            &class(),
            &memory,
            &PureFactContext::new(),
        ));
        let (CValue::Pointer(before), CValue::Pointer(after)) = (&original, &refined) else {
            unreachable!()
        };
        assert!(after.supports_object_class(&class()));
        assert_eq!(after.pointer(), before.pointer());
        assert_eq!(after.designation(), before.designation());
        assert_eq!(after.extent(), before.extent());
        assert_eq!(after.extent_is_known(), before.extent_is_known());
        assert_eq!(after.opaque_extent(), before.opaque_extent());

        let other = CAccessClass::Struct(CStructClass::opaque("other"));
        for (mut value, declared) in [
            (original.clone(), CMemory::new()),
            (
                make(Pointer {
                    offset: PointerOffsetTerm::Constant(4),
                    ..object
                }),
                memory.clone(),
            ),
            (
                original.with_pointer_object_class(Some(other)),
                memory.clone(),
            ),
        ] {
            assert!(!refine_object_pointer_argument(
                &mut value,
                &class(),
                &declared,
                &PureFactContext::new(),
            ));
        }
    }

    #[test]
    fn unrequired_formal_origins_survive_pointer_words_without_becoming_type_evidence() {
        let value =
            CValue::typed_pointer(Pointer::symbolic(Variable(900_001)), CType::Int32Pointer)
                .with_contract_pointer_object_class(Some(class()), None, 0, 42);
        let CValue::Pointer(pointer) = value else {
            unreachable!()
        };
        assert!(!pointer.supports_object_class(&class()));
        let context = PureFactContext::new();
        let word = super::super::eval::cast_c_value_to_type(
            CValue::Pointer(pointer.clone()),
            CType::UInt64,
            super::super::eval::IntegerConversion::Modular,
            &mut Vec::new(),
            &context,
        )
        .unwrap();
        assert!(matches!(word, CValue::PointerInteger(_)));
        let decoded = super::super::eval::cast_c_value_to_type(
            word,
            CType::Int32Pointer,
            super::super::eval::IntegerConversion::Modular,
            &mut Vec::new(),
            &context,
        )
        .unwrap();
        let CValue::Pointer(decoded) = decoded else {
            unreachable!()
        };
        assert!(!decoded.supports_object_class(&class()));
        assert_eq!(
            decoded.object_origin_evidence(),
            pointer.object_origin_evidence()
        );
    }
    #[test]
    fn numeric_address_annotations_cannot_manufacture_nominal_type_evidence() {
        let _session = crate::kernel::VerificationSession::enter();
        let original =
            CValue::typed_pointer(Pointer::symbolic(Variable(900_002)), CType::Int32Pointer)
                .with_pointer_object_class(Some(class()));
        let CValue::Pointer(source) = &original else {
            unreachable!()
        };
        let bits = Bitvector32Term::object_pointer_address(
            source.pointer().clone(),
            source.object_class(),
        );
        let decoded = super::super::eval::pointer_tags::cast_tagged_address_to_pointer(
            &bits,
            &PureFactContext::new(),
            &mut Vec::new(),
            CType::Int32Pointer,
        )
        .unwrap()
        .unwrap();
        assert_eq!(decoded.object_class(), Some(class()));
        assert!(!decoded.supports_object_class(&class()));
        let mut decoded = CValue::Pointer(decoded);
        let facts = PureFactContext::new().assume_proposition(Proposition::Predicate {
            name: "checked_source".into(),
            arguments: vec![Term::CValue(original.clone())],
        });
        assert!(refine_object_pointer_argument(
            &mut decoded,
            &class(),
            &CMemory::new(),
            &facts
        ));
        let word = super::super::eval::cast_c_value_to_type(
            original,
            CType::UInt64,
            super::super::eval::IntegerConversion::Modular,
            &mut Vec::new(),
            &PureFactContext::new(),
        )
        .unwrap();
        let decoded = super::super::eval::cast_c_value_to_type(
            word,
            CType::Int32Pointer,
            super::super::eval::IntegerConversion::Modular,
            &mut Vec::new(),
            &PureFactContext::new(),
        )
        .unwrap();
        assert!(
            matches!(decoded, CValue::Pointer(pointer) if pointer.supports_object_class(&class()))
        );
    }

    #[test]
    fn returned_alternatives_combine_origins_without_demanding_equal_origin_ids() {
        let values: Vec<_> = (0..2)
            .map(|index| {
                PureFunctionArgument::Value(
                    CValue::typed_pointer(
                        Pointer::symbolic(Variable(900_002 + index as u64)),
                        CType::Int32Pointer,
                    )
                    .with_contract_pointer_object_class(
                        Some(class()),
                        Some(class()),
                        index,
                        43,
                    ),
                )
            })
            .collect();
        let summary = PurePointerResult {
            classes: Default::default(),
            arguments: BTreeSet::from([0, 1]),
        };
        let (_, evidence) = pure_pointer_result_class(Some(&summary), &values);
        let evidence = evidence.unwrap();
        assert!(evidence.has_class(&class()));
        assert_eq!(evidence.premises.len(), 2);
    }
    mod scaling_tests {
        include!("../scaling_tests/kernel/object_types/tests.rs");
    }
}
