//! Explicit transport certificates. No history or premise discovery belongs here.
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
    pub(crate) fn check(
        &self,
        goal: &Proposition,
        available: impl Fn(&Proposition) -> bool,
    ) -> Result<(), String> {
        let mut results: Vec<&Proposition> = Vec::with_capacity(self.nodes.len());
        for (index, node) in self.nodes.iter().enumerate() {
            crate::instrumentation::record_deterministic_work(1);
            let prior = |n: usize| {
                results
                    .get(n)
                    .copied()
                    .ok_or_else(|| format!("node {index} must reference an earlier node"))
            };
            let result = match node {
                TransportNode::Premise {
                    proposition,
                    result,
                } => {
                    if proposition != result || !available(proposition) {
                        return Err(format!("premise node {index} is not exactly available"));
                    }
                    result
                }
                TransportNode::Preserve {
                    effect,
                    separation,
                    result,
                } => {
                    if !preserve(prior(*effect)?, prior(*separation)?, result) {
                        return Err(format!(
                            "preserve node {index} does not follow from the cited transition and separation"
                        ));
                    }
                    result
                }
                TransportNode::Transitive {
                    left,
                    right,
                    result,
                } => {
                    if !transitive(prior(*left)?, prior(*right)?, result) {
                        return Err(format!(
                            "transitive node {index} has mismatched equality endpoints"
                        ));
                    }
                    result
                }
            };
            results.push(result);
        }
        if results.get(self.conclusion).copied() != Some(goal) {
            return Err("transport conclusion does not match the goal".into());
        }
        Ok(())
    }
}

fn preserve(effect: &Proposition, separation: &Proposition, result: &Proposition) -> bool {
    let Proposition::CMemoryMutatesOnly {
        before,
        after,
        writes,
    } = effect
    else {
        return false;
    };
    let Proposition::CResourceSeparate { left, right } = separation else {
        return false;
    };
    // Each orientation is explicit and constant in number. This first rule
    // supports one complete typed cell beside an exactly stated write footprint.
    [
        (left.as_ref(), right.as_ref()),
        (right.as_ref(), left.as_ref()),
    ]
    .into_iter()
    .any(|(changed, kept)| {
        let (CResource::Memory(changed), CResource::Memory(kept)) = (changed, kept) else {
            return false;
        };
        let (written, write_bytes) = changed.byte_footprint();
        let Some(write_bytes) = write_bytes.as_const() else {
            return false;
        };
        if writes.len() != 1 || writes[0] != (written, write_bytes) {
            return false;
        }
        let (address, bytes) = kept.byte_footprint();
        let Some(bytes) = bytes.as_const() else {
            return false;
        };
        match result {
            Proposition::ConditionIs(ConditionTerm::PointerEqual(a, b), true)
                if bytes == C_POINTER_BYTE_WIDTH =>
            {
                pointer_address_at(after, &address).as_ref() == Some(a.as_ref())
                    && pointer_address_at(before, &address).as_ref() == Some(b.as_ref())
            }
            Proposition::ConditionIs(ConditionTerm::PointerValueEqual(a, b), true)
                if bytes == C_POINTER_BYTE_WIDTH && a.c_type() == b.c_type() =>
            {
                pointer_value_at(after, &address, a.c_type()).as_ref() == Some(a.as_ref())
                    && pointer_value_at(before, &address, b.c_type()).as_ref() == Some(b.as_ref())
            }
            Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format,
                    relation: CompareRelation::Equal,
                    left,
                    right,
                },
                true,
            ) => {
                scalar_value_at(after, &address, *format, bytes).map(|t| scalar_read_term(&t))
                    == Some(scalar_read_term(left))
                    && scalar_value_at(before, &address, *format, bytes)
                        .map(|t| scalar_read_term(&t))
                        == Some(scalar_read_term(right))
            }
            _ => false,
        }
    })
}

// Equal complete pointer domains lower to numeric pointer equality. This
// reads the same exact cell as value preservation, without granting a domain.
fn pointer_address_at(memory: &CMemory, address: &Pointer) -> Option<Pointer> {
    match memory.load(address) {
        CExpressionOutcome::Value(CValue::Pointer(value)) => Some(value.pointer().clone()),
        CExpressionOutcome::Value(_) => None,
        _ => Some(Pointer::loaded_value(
            &crate::kernel::intern_c_memory(memory.clone()),
            address,
        )),
    }
}

/// Read only the exact cell index. An absent cache denotes a symbolic read of
/// this snapshot; no derivation link or alias candidate is inspected.
fn pointer_value_at(memory: &CMemory, address: &Pointer, ty: CType) -> Option<CPointerValue> {
    match memory.load(address) {
        CExpressionOutcome::Value(CValue::Pointer(value)) if value.c_type() == ty => Some(value),
        CExpressionOutcome::Value(_) => None,
        _ => Some(CPointerValue::new(
            Pointer::loaded_value(&crate::kernel::intern_c_memory(memory.clone()), address),
            ty,
        )),
    }
}

// A load variable names its recorded read. Expand that single name by its
// registry key, never by resolving the snapshot's memory derivation.
fn scalar_read_term(term: &Bitvector32Term) -> Bitvector32Term {
    match term {
        Bitvector32Term::Variable(variable) => {
            crate::kernel::eval::registered_load_origin_term_for_variable(variable)
                .unwrap_or_else(|| term.clone())
        }
        _ => term.clone(),
    }
}

fn scalar_value_at(
    memory: &CMemory,
    address: &Pointer,
    format: MachineIntegerType,
    bytes: u32,
) -> Option<Bitvector32Term> {
    if format.carrier_bytes() != bytes {
        return None;
    }
    let value = match memory.load(address) {
        CExpressionOutcome::Value(value) => value,
        _ if bytes == 4 => memory.symbolic_int32_load(address),
        _ if bytes == 8 => memory.symbolic_int64_load(address),
        _ => return None,
    };
    match value {
        CValue::Int32(t) | CValue::UInt32(t) if bytes == 4 => Some(t),
        CValue::Int64(t) | CValue::UInt64(t) if bytes == 8 => Some(t),
        _ => None,
    }
}

fn transitive(a: &Proposition, b: &Proposition, result: &Proposition) -> bool {
    match (a, b, result) {
        (
            Proposition::ConditionIs(ConditionTerm::PointerEqual(x, y), true),
            Proposition::ConditionIs(ConditionTerm::PointerEqual(y2, z), true),
            Proposition::ConditionIs(ConditionTerm::PointerEqual(x2, z2), true),
        ) => x == x2 && y == y2 && z == z2,
        (
            Proposition::ConditionIs(ConditionTerm::PointerValueEqual(x, y), true),
            Proposition::ConditionIs(ConditionTerm::PointerValueEqual(y2, z), true),
            Proposition::ConditionIs(ConditionTerm::PointerValueEqual(x2, z2), true),
        ) => x == x2 && y == y2 && z == z2,
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
            Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: h,
                    relation: CompareRelation::Equal,
                    left: x2,
                    right: z2,
                },
                true,
            ),
        ) => f == g && g == h && x == x2 && y == y2 && z == z2,
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
        let result = Proposition::ConditionIs(
            ConditionTerm::PointerValueEqual(
                Box::new(pointer_value_at(&after, &address, CType::Int32Pointer).unwrap()),
                Box::new(pointer_value_at(&before, &address, CType::Int32Pointer).unwrap()),
            ),
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
    fn preserve_checks_exact_footprint_endpoints_and_available_evidence() {
        let _session = crate::kernel::VerificationSession::enter();
        for cached in [false, true] {
            let (certificate, goal) = fixture(8, cached);
            assert!(certificate.check(&goal, |_| true).is_ok());
            assert!(certificate.check(&goal, |_| false).is_err());
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
            assert!(partial.check(&goal, |_| true).is_err());
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
                    broken.check(&goal, |_| true).is_err(),
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
