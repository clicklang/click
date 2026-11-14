//! Apply explicit transport nodes, constructing each result from its cited facts.
//! No history, read reconstruction, or premise discovery belongs here.
use crate::kernel::eval::typed_reads::{self, ReadType};
use crate::kernel::prelude::*;

#[derive(Clone, Debug)]
pub(crate) enum TransportNode {
    Premise {
        proposition: Proposition,
        result: Proposition,
    },
    Preserve {
        field: Option<typed_reads::FieldSelection>,
        effect: Option<usize>,
        separation: usize,
        result: Proposition,
    },
    Transitive {
        left: usize,
        right: usize,
        result: Proposition,
    },
}

pub(crate) struct TransportCertificate {
    pub nodes: Vec<TransportNode>,
    pub conclusion: usize,
}

impl TransportCertificate {
    pub(crate) fn apply(
        &self,
        available: impl Fn(&Proposition) -> bool,
    ) -> Result<Proposition, String> {
        let mut results: Vec<Proposition> = Vec::with_capacity(self.nodes.len());
        for (index, node) in self.nodes.iter().enumerate() {
            crate::instrumentation::record_deterministic_work(1);
            let prior = |n: usize| {
                results
                    .get(n)
                    .ok_or_else(|| format!("node {index} must reference an earlier node"))
            };
            let (derived, written) = match node {
                TransportNode::Premise {
                    proposition,
                    result,
                } => {
                    if !available(proposition) {
                        return Err(format!("premise node {index} is not exactly available"));
                    }
                    (proposition.clone(), result)
                }
                TransportNode::Preserve {
                    field,
                    effect,
                    separation,
                    result,
                } => {
                    let separation = prior(*separation)?;
                    if effect.is_none() {
                        let derived = if let Proposition::MemoryReadDefined { value_type, .. } =
                            result
                        {
                            let (before, after) = preserve_definedness(separation, *value_type)
                                .ok_or("preserve definedness requires a footprint separated from a complete typed cell")?;
                            if !available(&before) {
                                return Err(
                                    "preserve requires definedness at the footprint entry".into()
                                );
                            }
                            after
                        } else if let Some(field) = field {
                            preserve_field(separation, *field)
                                .ok_or("preserve requires the selected field of a resource separated from the footprint")?
                        } else if matches!(
                            result,
                            Proposition::ConditionIs(ConditionTerm::Constant(true), true)
                        ) {
                            result.clone()
                        } else {
                            preserve_footprint(separation, read_type(result).ok_or("unsupported footprint observation")?)
                                .ok_or("preserve requires a region footprint separated from the selected complete observation")?
                        };
                        if &derived != result {
                            return Err(format!(
                                "node {index}'s constructed result does not match its written result"
                            ));
                        }
                        results.push(derived);
                        continue;
                    }
                    let effect = prior(effect.unwrap())?;
                    let derived = match result {
                        // Lowering a reflexive 64-bit equality erases the
                        // observation to true. Introduce that constant fact;
                        // there is no remaining read to preserve or discover.
                        Proposition::ConditionIs(ConditionTerm::Constant(true), true)
                            if matches!(effect, Proposition::MemoryMutatesOnly { .. })
                                && matches!(separation, Proposition::ResourceSeparate { .. }) =>
                        {
                            Proposition::ConditionIs(ConditionTerm::Constant(true), true)
                        }
                        _ => {
                            let kind = read_type(result).ok_or_else(|| {
                                format!("preserve node {index} requires a supported typed equality")
                            })?;
                            preserve(effect, separation, kind)
                                .ok_or_else(|| format!("preserve node {index} requires a matching write footprint, separation, and recorded typed reads"))?
                        }
                    };
                    (derived, result)
                }
                TransportNode::Transitive {
                    left,
                    right,
                    result,
                } => {
                    let derived = transitive(prior(*left)?, prior(*right)?).ok_or_else(|| {
                        format!("transitive node {index} has mismatched equality endpoints")
                    })?;
                    (derived, result)
                }
            };
            // Connect the constructed result to the user's annotation. This
            // is syntactic equality, not a second derivation or a search.
            if &derived != written {
                return Err(format!(
                    "node {index}'s constructed result does not match its written result"
                ));
            }
            results.push(derived);
        }
        results
            .get(self.conclusion)
            .cloned()
            .ok_or_else(|| "transport conclusion must select a node".into())
    }
}

// The written result selects only the observation's type. Its endpoints are
// never used to manufacture the primitive's conclusion.
fn read_type(result: &Proposition) -> Option<ReadType> {
    match result {
        Proposition::ConditionIs(ConditionTerm::AlgebraicEqual(a, b), true)
            if a.algebraic_type == b.algebraic_type =>
        {
            Some(ReadType::Abstract)
        }
        Proposition::ConditionIs(ConditionTerm::PointerEqual(..), true) => {
            Some(ReadType::PointerAddress)
        }
        Proposition::ConditionIs(ConditionTerm::PointerValueEqual(a, b), true)
            if a.c_type() == b.c_type() =>
        {
            Some(ReadType::Pointer(a.c_type()))
        }
        Proposition::ConditionIs(
            ConditionTerm::Compare {
                format,
                relation: CompareRelation::Equal,
                ..
            },
            true,
        ) if matches!(
            format,
            MachineIntegerType::Int8
                | MachineIntegerType::UInt8
                | MachineIntegerType::Int16
                | MachineIntegerType::UInt16
                | MachineIntegerType::Int32
                | MachineIntegerType::UInt32
                | MachineIntegerType::Int64
                | MachineIntegerType::UInt64
        ) =>
        {
            Some(ReadType::Integer(*format))
        }
        _ => None,
    }
}

/// A single separated write preserves the selected complete observation.
/// The read producer supplied its value, including pointer provenance; apply
/// this law directly to those values, without inspecting the memory DAG.
fn preserve(effect: &Proposition, separation: &Proposition, kind: ReadType) -> Option<Proposition> {
    let Proposition::MemoryMutatesOnly {
        before,
        after,
        writes,
    } = effect
    else {
        return None;
    };
    let [(written, write_bytes)] = writes.as_slice() else {
        return None;
    };
    let Proposition::ResourceSeparate { left, right } = separation else {
        return None;
    };
    let (Resource::Memory(left), Resource::Memory(right)) = (left.as_ref(), right.as_ref()) else {
        return None;
    };
    let left_footprint = left.byte_footprint();
    let right_footprint = right.byte_footprint();
    let is_write = |(address, bytes): &(Pointer, MachineTerm)| {
        address == written && bytes.as_const() == Some(*write_bytes)
    };
    let (address, bytes) = if is_write(&left_footprint) {
        right_footprint
    } else if is_write(&right_footprint) {
        left_footprint
    } else {
        return None;
    };
    let observed = observation_type(kind, bytes.as_const()?)?;
    observation_equality(before, after, address, observed, kind)
}

fn preserve_footprint(separation: &Proposition, kind: ReadType) -> Option<Proposition> {
    let Proposition::ResourceSeparate { left, right } = separation else {
        return None;
    };
    let (footprint, kept) = match (left.as_ref(), right.as_ref()) {
        (Resource::Footprint(fp), Resource::Memory(kept))
        | (Resource::Memory(kept), Resource::Footprint(fp)) => (fp, kept),
        _ => return None,
    };
    if kept.wide_bounds().is_some() {
        return None;
    }
    let (address, bytes) = kept.byte_footprint();
    let observed = observation_type(kind, bytes.as_const()?)?;
    observation_equality(&footprint.before, &footprint.after, address, observed, kind)
}

/// The footprint and separated cell determine both endpoints. The goal selects
/// only the read type; it cannot supply a different address or snapshot.
fn preserve_definedness(
    separation: &Proposition,
    value_type: ProgramType,
) -> Option<(Proposition, Proposition)> {
    crate::instrumentation::record_deterministic_work(1);
    let Proposition::ResourceSeparate { left, right } = separation else {
        return None;
    };
    let (footprint, kept) = match (left.as_ref(), right.as_ref()) {
        (Resource::Footprint(fp), Resource::Memory(kept))
        | (Resource::Memory(kept), Resource::Footprint(fp)) => (fp, kept),
        _ => return None,
    };
    if kept.wide_bounds().is_some() {
        return None;
    }
    let (pointer, bytes) = kept.byte_footprint();
    if bytes.as_const()? != value_type.byte_width() {
        return None;
    }
    let defined = |memory: &Memory| Proposition::MemoryReadDefined {
        memory: memory.clone(),
        pointer: pointer.clone(),
        value_type,
    };
    Some((defined(&footprint.before), defined(&footprint.after)))
}

// Resource field values are retained by the persistent resource contexts.
// Select one identity and one field from each endpoint; never unfold the
// resource, enumerate its other fields, or replay its modifications.
fn preserve_field(
    separation: &Proposition,
    field: typed_reads::FieldSelection,
) -> Option<Proposition> {
    let Proposition::ResourceSeparate { left, right } = separation else {
        return None;
    };
    let (footprint, kept) = match (left.as_ref(), right.as_ref()) {
        (Resource::Footprint(fp), Resource::Instance(kept))
        | (Resource::Instance(kept), Resource::Footprint(fp)) => (fp, kept),
        _ => return None,
    };
    if kept.identity() != field.identity {
        return None;
    }
    crate::instrumentation::record_deterministic_work(2);
    let before = footprint.before_resources.owned_instance(field.identity)?;
    let after = footprint.after_resources.owned_instance(field.identity)?;
    let a = after.fields().get(field.index)?;
    let b = before.fields().get(field.index)?;
    let condition = match (a, b) {
        (AlgebraicValue::Algebraic(a), AlgebraicValue::Algebraic(b))
            if a.algebraic_type == b.algebraic_type =>
        {
            return Some(if a == b {
                Proposition::ConditionIs(ConditionTerm::Constant(true), true)
            } else {
                Proposition::Equal(Term::Algebraic(a.clone()), Term::Algebraic(b.clone()))
            });
        }
        (AlgebraicValue::Integer(a), AlgebraicValue::Integer(b)) => {
            ConditionTerm::integer_equal(a.clone(), b.clone())
        }
        (
            AlgebraicValue::Program(ProgramValue::Parameter(a)),
            AlgebraicValue::Program(ProgramValue::Parameter(b)),
        ) if a.algebraic_type == b.algebraic_type => {
            ConditionTerm::AlgebraicEqual(a.clone(), b.clone())
        }
        (
            AlgebraicValue::Program(ProgramValue::Pointer(a)),
            AlgebraicValue::Program(ProgramValue::Pointer(b)),
        ) if a.c_type() == b.c_type() => ConditionTerm::pointer_value_equal(a.clone(), b.clone()),
        (
            AlgebraicValue::Program(ProgramValue::Int32(a)),
            AlgebraicValue::Program(ProgramValue::Int32(b)),
        ) => ConditionTerm::equal(a.clone(), b.clone()),
        // An 8-bit field value is native: its equality is at its own format.
        (
            AlgebraicValue::Program(ProgramValue::UInt8(a)),
            AlgebraicValue::Program(ProgramValue::UInt8(b)),
        ) => integer_equality(MachineIntegerType::UInt8, a.clone(), b.clone())?,
        (
            AlgebraicValue::Program(ProgramValue::UInt32(a)),
            AlgebraicValue::Program(ProgramValue::UInt32(b)),
        ) => ConditionTerm::uint32_equal(a.clone(), b.clone()),
        (
            AlgebraicValue::Program(ProgramValue::Int64(a)),
            AlgebraicValue::Program(ProgramValue::Int64(b)),
        ) => ConditionTerm::int64_equal(a.clone(), b.clone()),
        (
            AlgebraicValue::Program(ProgramValue::UInt64(a)),
            AlgebraicValue::Program(ProgramValue::UInt64(b)),
        ) => ConditionTerm::uint64_equal(a.clone(), b.clone()),
        _ => return None,
    };
    Some(Proposition::ConditionIs(condition, true))
}

// A comparison selects the read of its own format, and an 8- or 16-bit read
// compared natively is that read. C promotes an unsigned byte comparison to
// int32, comparing the reads' widenings, while the selected resource still
// describes one byte: that comparison selects the byte's `uint8` read. Select
// that exact producer record, not a four-byte read or a search for an
// alternative observation.
fn observation_type(comparison: ReadType, bytes: u32) -> Option<ReadType> {
    match (comparison, bytes) {
        (ReadType::Integer(MachineIntegerType::Int32), 1) => {
            Some(ReadType::Integer(MachineIntegerType::UInt8))
        }
        (kind, bytes) if kind.bytes() == bytes => Some(kind),
        _ => None,
    }
}

fn observation_equality(
    before: &Memory,
    after: &Memory,
    address: Pointer,
    kind: ReadType,
    comparison: ReadType,
) -> Option<Proposition> {
    let after = typed_reads::get(after, &address, kind)?;
    let before = typed_reads::get(before, &address, kind)?;
    // A promoted comparison of a byte read compares the reads' widenings.
    if let (ReadType::Integer(narrow), ReadType::Integer(MachineIntegerType::Int32)) =
        (kind, comparison)
        && narrow != MachineIntegerType::Int32
    {
        let widen =
            |value| MachineTerm::machine_integer_cast(narrow, MachineIntegerType::Int32, value);
        return Some(Proposition::ConditionIs(
            ConditionTerm::equal(widen(integer_bits(after)?), widen(integer_bits(before)?)),
            true,
        ));
    }
    let condition = match (kind, after, before) {
        (ReadType::Pointer(_), ProgramValue::Pointer(a), ProgramValue::Pointer(b)) => {
            ConditionTerm::pointer_value_equal(a, b)
        }
        (ReadType::PointerAddress, ProgramValue::Pointer(a), ProgramValue::Pointer(b)) => {
            ConditionTerm::pointer_equal(a.pointer().clone(), b.pointer().clone())
        }
        (ReadType::Abstract, ProgramValue::Parameter(a), ProgramValue::Parameter(b))
            if a.algebraic_type == b.algebraic_type =>
        {
            ConditionTerm::AlgebraicEqual(a, b)
        }
        (ReadType::Integer(format), a, b) => {
            integer_equality(format, integer_bits(a)?, integer_bits(b)?)?
        }
        _ => return None,
    };
    Some(Proposition::ConditionIs(condition, true))
}

fn integer_bits(value: ProgramValue) -> Option<MachineTerm> {
    match value {
        ProgramValue::Int8(t)
        | ProgramValue::UInt8(t)
        | ProgramValue::Int16(t)
        | ProgramValue::UInt16(t)
        | ProgramValue::Int32(t)
        | ProgramValue::UInt32(t)
        | ProgramValue::Int64(t)
        | ProgramValue::UInt64(t) => Some(t),
        _ => None,
    }
}

fn integer_equality(
    format: MachineIntegerType,
    left: MachineTerm,
    right: MachineTerm,
) -> Option<ConditionTerm> {
    Some(match format {
        MachineIntegerType::Int8
        | MachineIntegerType::UInt8
        | MachineIntegerType::Int16
        | MachineIntegerType::UInt16 => {
            ConditionTerm::machine_compare(format, CompareRelation::Equal, left, right)
        }
        MachineIntegerType::Int32 => ConditionTerm::equal(left, right),
        MachineIntegerType::UInt32 => ConditionTerm::uint32_equal(left, right),
        MachineIntegerType::Int64 | MachineIntegerType::UInt64 => {
            ConditionTerm::int64_equal(left, right)
        }
        _ => return None,
    })
}

fn transitive(a: &Proposition, b: &Proposition) -> Option<Proposition> {
    let truth = Proposition::ConditionIs(ConditionTerm::Constant(true), true);
    // A complete-pointer identity can lower either to true or to a retained
    // reflexive address equality. Both carry no new information: keep the
    // other cited equality without reconstructing the erased pointer domain.
    let identity = |p: &Proposition| {
        p == &truth
            || matches!(p,
            Proposition::ConditionIs(ConditionTerm::PointerEqual(x, y), true) if x == y)
    };
    let supported = |p: &Proposition| {
        matches!(
            p,
            Proposition::Equal(Term::Algebraic(_), Term::Algebraic(_))
        ) || read_type(p).is_some()
            || matches!(
                p,
                Proposition::ConditionIs(ConditionTerm::IntegerEqual(..), true)
            )
    };
    if identity(a) && (identity(b) || supported(b)) {
        return Some(b.clone());
    }
    if identity(b) && supported(a) {
        return Some(a.clone());
    }
    if let (
        Proposition::Equal(Term::Algebraic(x), Term::Algebraic(y)),
        Proposition::Equal(Term::Algebraic(y2), Term::Algebraic(z)),
    ) = (a, b)
        && y == y2
    {
        return Some(if x == z {
            truth
        } else {
            Proposition::Equal(Term::Algebraic(x.clone()), Term::Algebraic(z.clone()))
        });
    }
    let condition = match (a, b) {
        (
            Proposition::ConditionIs(ConditionTerm::AlgebraicEqual(x, y), true),
            Proposition::ConditionIs(ConditionTerm::AlgebraicEqual(y2, z), true),
        ) if y == y2 => ConditionTerm::AlgebraicEqual(x.clone(), z.clone()),
        (
            Proposition::ConditionIs(ConditionTerm::IntegerEqual(x, y), true),
            Proposition::ConditionIs(ConditionTerm::IntegerEqual(y2, z), true),
        ) if y == y2 => ConditionTerm::IntegerEqual(x.clone(), z.clone()),
        (
            Proposition::ConditionIs(ConditionTerm::PointerEqual(x, y), true),
            Proposition::ConditionIs(ConditionTerm::PointerEqual(y2, z), true),
        ) if y == y2 => ConditionTerm::pointer_equal((**x).clone(), (**z).clone()),
        (
            Proposition::ConditionIs(ConditionTerm::PointerValueEqual(x, y), true),
            Proposition::ConditionIs(ConditionTerm::PointerValueEqual(y2, z), true),
        ) if y == y2 => ConditionTerm::pointer_value_equal((**x).clone(), (**z).clone()),
        (
            Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: f,
                    relation: CompareRelation::Equal,
                    left: x,
                    right: y,
                },
                true,
            ),
            Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: g,
                    relation: CompareRelation::Equal,
                    left: y2,
                    right: z,
                },
                true,
            ),
        ) if f == g && y == y2 => integer_equality(*f, (**x).clone(), (**z).clone())?,
        _ => return None,
    };
    Some(Proposition::ConditionIs(condition, true))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reflexive_address_equality_composes_with_complete_pointer_equality() {
        let a = PointerValue::new(
            Pointer::symbolic(Variable(8_390_890)),
            ProgramType::Int32Pointer,
        );
        let b = PointerValue::new(
            Pointer::symbolic(Variable(8_390_891)),
            ProgramType::Int32Pointer,
        );
        let identity = Proposition::ConditionIs(
            ConditionTerm::PointerEqual(
                Box::new(a.pointer().clone()),
                Box::new(a.pointer().clone()),
            ),
            true,
        );
        let address_only = Proposition::ConditionIs(
            ConditionTerm::PointerEqual(
                Box::new(a.pointer().clone()),
                Box::new(b.pointer().clone()),
            ),
            true,
        );
        let complete = Proposition::ConditionIs(
            ConditionTerm::PointerValueEqual(Box::new(a), Box::new(b)),
            true,
        );
        assert_eq!(transitive(&identity, &complete), Some(complete.clone()));
        assert_eq!(transitive(&complete, &identity), Some(complete.clone()));
        assert!(transitive(&address_only, &complete).is_none());
    }

    pub(super) fn definedness_fixture(
        history: u64,
        ty: ProgramType,
    ) -> (TransportCertificate, Proposition, Proposition, Proposition) {
        let pointer = Pointer::symbolic(Variable(8_410_000));
        let mut memory = Memory::new();
        for i in 0..history {
            // Grow both related history and unrelated memory.
            memory = memory.store(
                pointer.clone(),
                ProgramValue::Int32(MachineTerm::constant(i as u32)),
            );
            memory = memory.store(
                Pointer::symbolic(Variable(8_420_000 + i)),
                ProgramValue::Int32(MachineTerm::constant(i as u32)),
            );
        }
        let before = ExecutionState::new().with_memory(memory.clone());
        let after = ExecutionState::new().with_memory(memory.store(
            Pointer::symbolic(Variable(8_430_000)),
            ProgramValue::Int32(1u32.into()),
        ));
        let footprint = crate::kernel::RegionFootprint::transition(
            "selected".into(),
            &before,
            &after,
            &Vec::<ExecutionPureFact>::new(),
        );
        let separation = Proposition::ResourceSeparate {
            left: Box::new(Resource::Footprint(footprint)),
            right: Box::new(Resource::Memory(MemoryRange::new_with_element_width(
                pointer.clone(),
                0u32.into(),
                1u32.into(),
                ty.byte_width(),
            ))),
        };
        let old = Proposition::MemoryReadDefined {
            memory: before.memory().clone(),
            pointer: pointer.clone(),
            value_type: ty,
        };
        let goal = Proposition::MemoryReadDefined {
            memory: after.memory().clone(),
            pointer,
            value_type: ty,
        };
        (
            TransportCertificate {
                nodes: vec![
                    TransportNode::Premise {
                        proposition: separation.clone(),
                        result: separation.clone(),
                    },
                    TransportNode::Preserve {
                        field: None,
                        effect: None,
                        separation: 0,
                        result: goal.clone(),
                    },
                ],
                conclusion: 1,
            },
            separation,
            old,
            goal,
        )
    }

    #[test]
    fn preserve_definedness_requires_exact_entry_evidence_and_complete_cell() {
        let _session = crate::kernel::VerificationSession::enter();
        for ty in [
            ProgramType::UInt8,
            ProgramType::Int32,
            ProgramType::UInt64,
            ProgramType::Int32Pointer,
        ] {
            let (mut certificate, separation, old, goal) = definedness_fixture(4, ty);
            let available = |p: &Proposition| p == &separation || p == &old;
            assert_eq!(certificate.apply(available).unwrap(), goal);
            assert!(
                certificate
                    .apply(|p| p == &separation)
                    .unwrap_err()
                    .contains("footprint entry")
            );
            assert!(certificate.apply(|p| p == &old).is_err());
            for corruption in 0..3 {
                let mut bad = goal.clone();
                let Proposition::MemoryReadDefined {
                    memory,
                    pointer,
                    value_type,
                } = &mut bad
                else {
                    unreachable!()
                };
                match corruption {
                    0 => *memory = Memory::new(),
                    1 => *pointer = Pointer::symbolic(Variable(8_499_000)),
                    _ => {
                        *value_type = if ty == ProgramType::UInt8 {
                            ProgramType::Int32
                        } else {
                            ProgramType::UInt8
                        }
                    }
                }
                let TransportNode::Preserve { result, .. } = &mut certificate.nodes[1] else {
                    unreachable!()
                };
                *result = bad;
                assert!(
                    certificate.apply(available).is_err(),
                    "corruption {corruption}"
                );
            }
            let mut swapped = separation.clone();
            let Proposition::ResourceSeparate { left, right } = &mut swapped else {
                unreachable!()
            };
            std::mem::swap(left, right);
            assert_eq!(preserve_definedness(&swapped, ty), Some((old, goal)));
        }
    }

    pub(super) fn resource_fixture(size: u64) -> (TransportCertificate, Proposition) {
        let schema = ResourceFieldSchema::new(vec![(
            "value".into(),
            ResourceFieldType::Program(ProgramType::Int32),
        )])
        .unwrap();
        let instance = |identity, value| {
            ResourceInstance::new(
                Variable(identity),
                "model".into(),
                vec![].into(),
                schema.clone(),
                vec![AlgebraicValue::Program(ProgramValue::Int32(
                    MachineTerm::Variable(Variable(value)),
                ))]
                .into(),
            )
            .unwrap()
        };
        let kept = instance(8_390_900, 8_390_901);
        let mut resources = ResourceContext::new();
        for i in 0..size {
            resources = resources.unchecked_with_fact(ResourceFact::own(Resource::Instance(
                instance(9_000_000 + i, 10_000_000 + i),
            )));
        }
        let before = ExecutionState::new().with_resource_context(
            resources
                .clone()
                .unchecked_with_fact(ResourceFact::own(Resource::Instance(kept.clone()))),
        );
        let after = ExecutionState::new().with_resource_context(resources.unchecked_with_fact(
            ResourceFact::own(Resource::Instance(instance(8_390_900, 8_390_902))),
        ));
        // A supplied frame premise relates these symbolic endpoint values.
        // As with the memory fixture, establishing the premise is a separate
        // obligation, never performed by certificate application.
        let footprint = crate::kernel::RegionFootprint::transition(
            "selected".into(),
            &before,
            &after,
            &Vec::<ExecutionPureFact>::new(),
        );
        let separation = Proposition::ResourceSeparate {
            left: Box::new(Resource::Footprint(footprint)),
            right: Box::new(Resource::Instance(kept)),
        };
        let goal = Proposition::ConditionIs(
            ConditionTerm::equal(
                MachineTerm::Variable(Variable(8_390_902)),
                MachineTerm::Variable(Variable(8_390_901)),
            ),
            true,
        );
        (
            TransportCertificate {
                nodes: vec![
                    TransportNode::Premise {
                        proposition: separation.clone(),
                        result: separation,
                    },
                    TransportNode::Preserve {
                        field: Some(typed_reads::FieldSelection {
                            identity: Variable(8_390_900),
                            index: 0,
                        }),
                        effect: None,
                        separation: 0,
                        result: goal.clone(),
                    },
                ],
                conclusion: 1,
            },
            goal,
        )
    }

    pub(super) fn resource_history_fixture(history: u64) -> (TransportCertificate, Proposition) {
        let (mut certificate, goal) = resource_fixture(1);
        let TransportNode::Premise {
            proposition,
            result,
        } = &mut certificate.nodes[0]
        else {
            unreachable!()
        };
        let Proposition::ResourceSeparate { left, right } = proposition else {
            unreachable!()
        };
        let Resource::Footprint(fp) = left.as_ref() else {
            unreachable!()
        };
        let Resource::Instance(kept) = right.as_ref() else {
            unreachable!()
        };
        let mut resources = fp.before_resources.clone();
        for _ in 0..history {
            let fact = ResourceFact::own(Resource::Instance(kept.clone()));
            resources = resources
                .without_exact_representation(&fact)
                .unwrap()
                .unchecked_with_fact(fact);
        }
        let before = ExecutionState::new().with_resource_context(resources);
        let after = ExecutionState::new().with_resource_context(fp.after_resources.clone());
        **left = Resource::Footprint(crate::kernel::RegionFootprint::transition(
            "selected".into(),
            &before,
            &after,
            &Vec::<ExecutionPureFact>::new(),
        ));
        *result = proposition.clone();
        (certificate, goal)
    }

    #[test]
    fn resource_preservation_selects_exact_identity_field_and_values() {
        let (certificate, goal) = resource_fixture(8);
        assert_eq!(certificate.apply(|_| true).unwrap(), goal);
        assert!(
            certificate.apply(|_| false).is_err(),
            "separation must be available"
        );
        for field in [
            typed_reads::FieldSelection {
                identity: Variable(8_390_999),
                index: 0,
            },
            typed_reads::FieldSelection {
                identity: Variable(8_390_900),
                index: 1,
            },
        ] {
            let (mut certificate, _) = resource_fixture(8);
            let TransportNode::Preserve {
                field: selected, ..
            } = &mut certificate.nodes[1]
            else {
                unreachable!()
            };
            *selected = Some(field);
            assert!(certificate.apply(|_| true).is_err());
        }
        let (mut certificate, _) = resource_fixture(8);
        let TransportNode::Preserve { result, .. } = &mut certificate.nodes[1] else {
            unreachable!()
        };
        *result = Proposition::ConditionIs(
            ConditionTerm::equal(MachineTerm::Variable(Variable(8_390_902)), 99u32.into()),
            true,
        );
        assert!(
            certificate.apply(|_| true).is_err(),
            "the annotation cannot invent a value"
        );
    }

    pub(super) fn observe(memory: &Memory, address: &Pointer, ty: ProgramType) -> ProgramValue {
        let paths = crate::kernel::eval::evaluate_logical_memory_load_paths(
            memory,
            address.clone(),
            ty,
            Default::default(),
            Vec::new(),
            &PureFactContext::new(),
        );
        let [path] = paths.as_slice() else {
            panic!("one logical read");
        };
        let ExpressionOutcome::Value(value) = &path.outcome else {
            panic!("logical value");
        };
        value.clone()
    }

    pub(super) fn fixture(history: u64, cached: bool) -> (TransportCertificate, Proposition) {
        let address = Pointer::symbolic(Variable(8_310_000));
        let changed = Pointer::symbolic(Variable(8_310_001));
        let mut before = Memory::new();
        for i in 0..history {
            before = before.store(
                Pointer::symbolic(Variable(8_320_000 + i)),
                ProgramValue::Int32(MachineTerm::constant(i as u32)),
            );
        }
        if cached {
            before = before.store(
                address.clone(),
                ProgramValue::typed_pointer(
                    Pointer::symbolic(Variable(8_310_002)),
                    ProgramType::Int32Pointer,
                ),
            );
        }
        let after = before
            .clone()
            .without_possible_aliasing_cells(&changed, 4, &PureFactContext::new())
            .store(
                changed.clone(),
                ProgramValue::Int32(MachineTerm::constant(1)),
            );
        let resource = |p, bytes| {
            Box::new(Resource::Memory(MemoryRange::new_with_element_width(
                p,
                0u32.into(),
                1u32.into(),
                bytes,
            )))
        };
        let separation = Proposition::ResourceSeparate {
            left: resource(changed.clone(), 4),
            right: resource(address.clone(), C_POINTER_BYTE_WIDTH),
        };
        let ProgramValue::Pointer(before_value) =
            observe(&before, &address, ProgramType::Int32Pointer)
        else {
            unreachable!()
        };
        let ProgramValue::Pointer(after_value) =
            observe(&after, &address, ProgramType::Int32Pointer)
        else {
            unreachable!()
        };
        let result = Proposition::ConditionIs(
            ConditionTerm::pointer_value_equal(after_value, before_value),
            true,
        );
        let effect = Proposition::MemoryMutatesOnly {
            before,
            after,
            writes: vec![(changed, 4)],
        };
        let premise = |p: Proposition| TransportNode::Premise {
            proposition: p.clone(),
            result: p,
        };
        (
            TransportCertificate {
                nodes: vec![
                    premise(effect),
                    premise(separation),
                    TransportNode::Preserve {
                        field: None,
                        effect: Some(0),
                        separation: 1,
                        result: result.clone(),
                    },
                ],
                conclusion: 2,
            },
            result,
        )
    }

    pub(super) fn abstract_fixture(history: u64) -> (TransportCertificate, Proposition) {
        let (mut certificate, _) = fixture(history, false);
        let TransportNode::Premise {
            proposition: Proposition::MemoryMutatesOnly { before, after, .. },
            ..
        } = &certificate.nodes[0]
        else {
            unreachable!()
        };
        let address = Pointer::symbolic(Variable(8_310_000));
        let ty = ProgramType::Parameter(TypeParameterName::intern("TransportValue"));
        let ProgramValue::Parameter(a) = observe(after, &address, ty) else {
            unreachable!()
        };
        let ProgramValue::Parameter(b) = observe(before, &address, ty) else {
            unreachable!()
        };
        let goal = Proposition::ConditionIs(ConditionTerm::AlgebraicEqual(a, b), true);
        let TransportNode::Preserve { result, .. } = &mut certificate.nodes[2] else {
            unreachable!()
        };
        *result = goal.clone();
        (certificate, goal)
    }

    #[test]
    fn abstract_memory_preservation_uses_recorded_typed_values() {
        let _session = crate::kernel::VerificationSession::enter();
        let _reads = typed_reads::ReadScope::enter();
        let (mut certificate, goal) = abstract_fixture(8);
        assert_eq!(certificate.apply(|_| true).unwrap(), goal);
        let TransportNode::Preserve { result, .. } = &mut certificate.nodes[2] else {
            unreachable!()
        };
        let Proposition::ConditionIs(ConditionTerm::AlgebraicEqual(_, old), true) = result else {
            unreachable!()
        };
        old.algebraic_type = TypeParameterName::intern("WrongTransportValue").algebraic_type();
        assert!(
            certificate.apply(|_| true).is_err(),
            "abstract types must agree"
        );
        let (certificate, _) = abstract_fixture(8);
        let _empty_reads = typed_reads::ReadScope::enter();
        assert!(
            certificate.apply(|_| true).is_err(),
            "no reconstruction when observations are absent"
        );
    }

    #[test]
    fn preserve_constructs_its_result_independently_of_the_annotation() {
        let _session = crate::kernel::VerificationSession::enter();
        let _reads = typed_reads::ReadScope::enter();
        let (mut certificate, goal) = fixture(8, false);
        let TransportNode::Premise {
            proposition: effect,
            ..
        } = &certificate.nodes[0]
        else {
            unreachable!()
        };
        let TransportNode::Premise {
            proposition: separation,
            ..
        } = &certificate.nodes[1]
        else {
            unreachable!()
        };
        assert_eq!(
            preserve(effect, separation, read_type(&goal).unwrap()),
            Some(goal)
        );
        let mut wrong_domain = TransportCertificate {
            nodes: certificate.nodes.clone(),
            conclusion: certificate.conclusion,
        };
        let TransportNode::Preserve {
            result: Proposition::ConditionIs(ConditionTerm::PointerValueEqual(left, _), true),
            ..
        } = &mut wrong_domain.nodes[2]
        else {
            panic!("distinct complete read domains");
        };
        **left = (**left)
            .clone()
            .with_designation(std::sync::Arc::new(Pointer::symbolic(Variable(8_399_099))));
        assert!(
            wrong_domain
                .apply(|_| true)
                .unwrap_err()
                .contains("constructed result")
        );
        let TransportNode::Preserve { result, .. } = &mut certificate.nodes[2] else {
            unreachable!()
        };
        *result = Proposition::ConditionIs(
            ConditionTerm::PointerEqual(
                Box::new(Pointer::symbolic(Variable(8_399_000))),
                Box::new(Pointer::symbolic(Variable(8_399_001))),
            ),
            true,
        );
        assert!(
            certificate
                .apply(|_| true)
                .unwrap_err()
                .contains("constructed result")
        );
    }

    #[test]
    fn typed_read_observations_are_scoped_and_keep_the_selected_width() {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = Memory::new();
        let address = Pointer::symbolic(Variable(8_399_010));
        let kind = ReadType::Integer(MachineIntegerType::Int64);
        observe(&memory, &address, ProgramType::UInt64);
        assert!(typed_reads::get(&memory, &address, kind).is_none());
        {
            let _outer = typed_reads::ReadScope::enter();
            let value = observe(&memory, &address, ProgramType::UInt64);
            assert_eq!(
                typed_reads::get(&memory, &address, kind),
                Some(value.numeric_value().clone())
            );
            assert!(typed_reads::get(&memory, &address, ReadType::PointerAddress).is_none());
            assert!(
                typed_reads::get(
                    &memory,
                    &address,
                    ReadType::Integer(MachineIntegerType::Int32)
                )
                .is_none()
            );
            {
                let _inner = typed_reads::ReadScope::enter();
                assert!(typed_reads::get(&memory, &address, kind).is_none());
                observe(&memory, &address, ProgramType::Int32);
            }
            assert_eq!(
                typed_reads::get(&memory, &address, kind),
                Some(value.numeric_value().clone())
            );
            assert!(
                typed_reads::get(
                    &memory,
                    &address,
                    ReadType::Integer(MachineIntegerType::Int32)
                )
                .is_none()
            );
        }
        assert!(typed_reads::get(&memory, &address, kind).is_none());
    }

    #[test]
    fn preserve_checks_exact_footprint_endpoints_and_available_evidence() {
        let _session = crate::kernel::VerificationSession::enter();
        let _reads = typed_reads::ReadScope::enter();
        for cached in [false, true] {
            let (certificate, goal) = fixture(8, cached);
            assert_eq!(certificate.apply(|_| true).unwrap(), goal);
            assert!(certificate.apply(|_| false).is_err());
            let mut partial = TransportCertificate {
                nodes: certificate.nodes.clone(),
                conclusion: 2,
            };
            let TransportNode::Premise {
                proposition,
                result,
            } = &mut partial.nodes[1]
            else {
                unreachable!()
            };
            let Proposition::ResourceSeparate { right, .. } = proposition else {
                unreachable!()
            };
            let Resource::Memory(range) = right.as_ref() else {
                unreachable!()
            };
            let (address, _) = range.byte_footprint();
            **right = Resource::Memory(MemoryRange::new_with_element_width(
                address,
                0u32.into(),
                1u32.into(),
                1,
            ));
            *result = proposition.clone();
            assert!(partial.apply(|_| true).is_err());
            for corruption in 0..4 {
                let mut broken = TransportCertificate {
                    nodes: certificate.nodes.clone(),
                    conclusion: 2,
                };
                let TransportNode::Premise {
                    proposition,
                    result,
                } = &mut broken.nodes[0]
                else {
                    unreachable!()
                };
                let Proposition::MemoryMutatesOnly {
                    before,
                    after,
                    writes,
                } = proposition
                else {
                    unreachable!()
                };
                match corruption {
                    0 => writes[0].1 = 1,
                    1 => writes.push(writes[0].clone()),
                    2 => writes[0].0 = Pointer::symbolic(Variable(8_310_099)),
                    _ => {
                        *before = Memory::new();
                        *after = Memory::new();
                    }
                }
                *result = proposition.clone();
                assert!(
                    broken.apply(|_| true).is_err(),
                    "corruption {corruption}, cached={cached}"
                );
            }
        }
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/proof/transport_certificate.rs");
}
