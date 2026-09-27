//! A declared exclusive resource assertion without an owned occurrence.
//!
//! A description retains the resource family, evaluated parameters, and field
//! schema. It contains no instance identity, observed field values, or proof
//! of ownership. Consumers must check an owned instance separately.

use super::{
    AlgebraicValue, PureFactContext, ResourceArguments, ResourceFieldSchema, ResourceInstance,
};
use std::sync::Arc;

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct ResourceDescription(Arc<ResourceDescriptionData>);

#[derive(Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
struct ResourceDescriptionData {
    family: String,
    arguments: ResourceArguments,
    schema: ResourceFieldSchema,
}

impl ResourceDescription {
    /// Describe a checked exclusive instance without retaining its binder or
    /// the values observed in its fields.
    pub fn from_instance(instance: &ResourceInstance) -> Self {
        Self(Arc::new(ResourceDescriptionData {
            family: instance.name.clone(),
            arguments: instance.arguments.clone(),
            schema: instance.schema.clone(),
        }))
    }

    pub fn family(&self) -> &str {
        &self.0.family
    }

    pub fn arguments(&self) -> &[AlgebraicValue] {
        &self.0.arguments
    }

    pub fn schema(&self) -> &ResourceFieldSchema {
        &self.0.schema
    }

    /// Check the full description without requiring an earlier occurrence or
    /// earlier observations. Argument equality uses the same checked relation
    /// as ordinary resource contracts. This supplies no ownership evidence.
    pub fn matches_instance(
        &self,
        instance: &ResourceInstance,
        assumptions: &PureFactContext,
    ) -> bool {
        self.family() == instance.name()
            && self.schema() == instance.schema()
            && self.arguments().len() == instance.arguments().len()
            && self
                .arguments()
                .iter()
                .zip(instance.arguments())
                .all(|(left, right)| {
                    left == right
                        || super::resource_arguments_proven_equal(left, right, assumptions)
                })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{CType, ResourceFieldType, Variable, int32};
    use std::collections::BTreeSet;
    use std::hash::{Hash, Hasher};

    fn instance(identity: u64, family: &str, argument: u32, observed: u32) -> ResourceInstance {
        ResourceInstance::new(
            Variable(identity),
            family.into(),
            vec![int32(argument).into()].into(),
            ResourceFieldSchema::new(vec![("value".into(), ResourceFieldType::C(CType::Int32))])
                .unwrap(),
            vec![int32(observed).into()].into(),
        )
        .unwrap()
    }

    fn hash(description: &ResourceDescription) -> u64 {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        description.hash(&mut hasher);
        hasher.finish()
    }

    #[test]
    fn description_has_exact_family_arguments_and_schema_without_observations() {
        let first = instance(1, "state", 7, 10);
        let later = instance(2, "state", 7, 20);
        let description = ResourceDescription::from_instance(&first);
        assert_eq!(description, ResourceDescription::from_instance(&later));
        assert_eq!(
            hash(&description),
            hash(&ResourceDescription::from_instance(&later))
        );
        assert_eq!(description.family(), "state");
        assert_eq!(description.arguments(), first.arguments());
        assert_eq!(description.schema(), first.schema());
        assert_ne!(
            description,
            ResourceDescription::from_instance(&instance(3, "other", 7, 10))
        );
        assert_ne!(
            description,
            ResourceDescription::from_instance(&instance(3, "state", 8, 10))
        );
        let mut different_schema = later;
        different_schema.schema =
            ResourceFieldSchema::new(vec![("other".into(), ResourceFieldType::C(CType::Int32))])
                .unwrap();
        assert_ne!(
            description,
            ResourceDescription::from_instance(&different_schema)
        );
        assert_eq!(
            BTreeSet::from([
                description.clone(),
                ResourceDescription::from_instance(&different_schema)
            ])
            .len(),
            2
        );
    }

    #[test]
    fn cloning_a_description_shares_storage_independently_of_argument_count() {
        let mut work = Vec::new();
        for size in [16, 64, 256] {
            let instance = ResourceInstance::new(
                Variable(1),
                "state".into(),
                (0..size)
                    .map(|index| int32(index).into())
                    .collect::<Vec<_>>()
                    .into(),
                ResourceFieldSchema::new(vec![(
                    "value".into(),
                    ResourceFieldType::C(CType::Int32),
                )])
                .unwrap(),
                vec![int32(1).into()].into(),
            )
            .unwrap();
            let description = ResourceDescription::from_instance(&instance);
            let ((clone, deterministic), persistent) =
                crate::persistent::measure_persistent_work(|| {
                    crate::instrumentation::measure_deterministic_work(|| description.clone())
                });
            assert!(Arc::ptr_eq(&description.0, &clone.0));
            assert_eq!(clone.arguments().len(), size as usize);
            work.push((deterministic, persistent));
        }
        assert!(work.windows(2).all(|pair| pair[1] == pair[0]), "{work:?}");
    }
}
