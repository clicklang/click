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
        effect: usize,
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
                    effect,
                    separation,
                    result,
                } => {
                    let effect = prior(*effect)?;
                    let separation = prior(*separation)?;
                    let derived = match result {
                        // Lowering a reflexive 64-bit equality erases the
                        // observation to true. Introduce that constant fact;
                        // there is no remaining read to preserve or discover.
                        Proposition::ConditionIs(ConditionTerm::Constant(true), true)
                            if matches!(effect, Proposition::CMemoryMutatesOnly { .. })
                                && matches!(separation, Proposition::CResourceSeparate { .. }) =>
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
            MachineIntegerType::Int32
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
    let Proposition::CMemoryMutatesOnly {
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
    let Proposition::CResourceSeparate { left, right } = separation else {
        return None;
    };
    let (CResource::Memory(left), CResource::Memory(right)) = (left.as_ref(), right.as_ref())
    else {
        return None;
    };
    let left_footprint = left.byte_footprint();
    let right_footprint = right.byte_footprint();
    let is_write = |(address, bytes): &(Pointer, Bitvector32Term)| {
        address == written && bytes.as_const() == Some(*write_bytes)
    };
    let (address, bytes) = if is_write(&left_footprint) {
        right_footprint
    } else if is_write(&right_footprint) {
        left_footprint
    } else {
        return None;
    };
    if bytes.as_const() != Some(kind.bytes()) {
        return None;
    }
    let after = typed_reads::get(after, &address, kind)?;
    let before = typed_reads::get(before, &address, kind)?;
    let condition = match (kind, after, before) {
        (ReadType::Pointer(_), CValue::Pointer(a), CValue::Pointer(b)) => {
            ConditionTerm::pointer_value_equal(a, b)
        }
        (ReadType::PointerAddress, CValue::Pointer(a), CValue::Pointer(b)) => {
            ConditionTerm::pointer_equal(a.pointer().clone(), b.pointer().clone())
        }
        (ReadType::Integer(format), a, b) => {
            integer_equality(format, integer_bits(a)?, integer_bits(b)?)?
        }
        _ => return None,
    };
    Some(Proposition::ConditionIs(condition, true))
}

fn integer_bits(value: CValue) -> Option<Bitvector32Term> {
    match value {
        CValue::Int32(t) | CValue::UInt32(t) | CValue::Int64(t) | CValue::UInt64(t) => Some(t),
        _ => None,
    }
}

fn integer_equality(
    format: MachineIntegerType,
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Option<ConditionTerm> {
    Some(match format {
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
    // Reflexive equalities may already have reduced to true. Composition
    // then retains the other cited equality, with no endpoint to rediscover.
    if a == &truth && (b == &truth || read_type(b).is_some()) {
        return Some(b.clone());
    }
    if b == &truth && read_type(a).is_some() {
        return Some(a.clone());
    }
    let condition = match (a, b) {
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

    pub(super) fn observe(memory: &CMemory, address: &Pointer, ty: CType) -> CValue {
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
        let CExpressionOutcome::Value(value) = &path.outcome else {
            panic!("logical value");
        };
        value.clone()
    }

    pub(super) fn fixture(history: u64, cached: bool) -> (TransportCertificate, Proposition) {
        let address = Pointer::symbolic(Variable(8_310_000));
        let changed = Pointer::symbolic(Variable(8_310_001));
        let mut before = CMemory::new();
        for i in 0..history {
            before = before.store(
                Pointer::symbolic(Variable(8_320_000 + i)),
                CValue::Int32(Bitvector32Term::Constant(i as u32)),
            );
        }
        if cached {
            before = before.store(
                address.clone(),
                CValue::typed_pointer(Pointer::symbolic(Variable(8_310_002)), CType::Int32Pointer),
            );
        }
        let after = before
            .clone()
            .without_possible_aliasing_cells(&changed, 4, &PureFactContext::new())
            .store(changed.clone(), CValue::Int32(Bitvector32Term::Constant(1)));
        let resource = |p, bytes| {
            Box::new(CResource::Memory(CMemoryRange::new_with_element_width(
                p,
                0u32.into(),
                1u32.into(),
                bytes,
            )))
        };
        let separation = Proposition::CResourceSeparate {
            left: resource(changed.clone(), 4),
            right: resource(address.clone(), C_POINTER_BYTE_WIDTH),
        };
        let CValue::Pointer(before_value) = observe(&before, &address, CType::Int32Pointer) else {
            unreachable!()
        };
        let CValue::Pointer(after_value) = observe(&after, &address, CType::Int32Pointer) else {
            unreachable!()
        };
        let result = Proposition::ConditionIs(
            ConditionTerm::pointer_value_equal(after_value, before_value),
            true,
        );
        let effect = Proposition::CMemoryMutatesOnly {
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
                        effect: 0,
                        separation: 1,
                        result: result.clone(),
                    },
                ],
                conclusion: 2,
            },
            result,
        )
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
        let memory = CMemory::new();
        let address = Pointer::symbolic(Variable(8_399_010));
        let kind = ReadType::Integer(MachineIntegerType::Int64);
        observe(&memory, &address, CType::UInt64);
        assert!(typed_reads::get(&memory, &address, kind).is_none());
        {
            let _outer = typed_reads::ReadScope::enter();
            let value = observe(&memory, &address, CType::UInt64);
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
                observe(&memory, &address, CType::Int32);
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
            let Proposition::CResourceSeparate { right, .. } = proposition else {
                unreachable!()
            };
            let CResource::Memory(range) = right.as_ref() else {
                unreachable!()
            };
            let (address, _) = range.byte_footprint();
            *right = Box::new(CResource::Memory(CMemoryRange::new_with_element_width(
                address,
                0u32.into(),
                1u32.into(),
                1,
            )));
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
                let Proposition::CMemoryMutatesOnly {
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
                        *before = CMemory::new();
                        *after = CMemory::new();
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
