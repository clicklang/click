//! Pointer representation-independent checking policy. Address equality is not
//! provenance or bounds evidence. Callers retain the existing checked authority
//! for each relation; these readers neither search nor create evidence.
use super::*;
use crate::kernel::{
    KernelPointerOffset as O, KernelTerm, KernelType, MachineOperandView as V,
    SharedPointerAddress, SharedPointerOffset, SharedPointerValue,
};
use std::collections::{HashMap, HashSet};

pub(super) struct Origins<'a, A, W> {
    pub(super) provenance: &'a A,
    pub(super) opaque: Option<&'a A>,
    pub(super) bounds: Option<(&'a A, &'a W)>,
    pub(super) known: bool,
}
impl<'a> Origins<'a, Pointer, MachineTerm> {
    pub(super) fn native(value: &'a PointerValue) -> Self {
        Self {
            provenance: value.provenance(),
            opaque: value.bounds_owner(),
            bounds: value.bounds().map(|e| (&e.start, &e.width)),
            known: value.bounds_are_known(),
        }
    }
}
impl<'a> Origins<'a, SharedPointerAddress, KernelTerm> {
    pub(super) fn shared(value: &'a SharedPointerValue) -> Self {
        let p = value.node();
        let q = p.qualifiers.as_ref();
        Self {
            provenance: &p.provenance,
            opaque: p.bounds_owner.as_ref(),
            bounds: q
                .and_then(|q| q.bounds.as_ref())
                .map(|e| (&e.start, &e.width)),
            known: q.is_some_and(|q| q.bounds_known),
        }
    }
}
/// Each method is a different existing authority, not interchangeable aliases.
pub(super) trait OriginChecks<A, W> {
    fn provenance(&self, a: &A, b: &A) -> bool;
    fn opaque(&self, a: &A, b: &A) -> bool;
    fn address(&self, a: &A, b: &A) -> bool;
    fn width(&self, a: &W, b: &W) -> bool;
    fn opaque_is_root(&self, a: &A) -> bool;
}
impl OriginChecks<Pointer, MachineTerm> for PureFactContext {
    fn provenance(&self, a: &Pointer, b: &Pointer) -> bool {
        self.provenance_equal(a, b)
    }
    fn opaque(&self, a: &Pointer, b: &Pointer) -> bool {
        self.bounds_owners_equal(a, b)
    }
    fn address(&self, a: &Pointer, b: &Pointer) -> bool {
        self.equality_graph.are_equal(a, b)
    }
    fn width(&self, a: &MachineTerm, b: &MachineTerm) -> bool {
        a == b
    }
    fn opaque_is_root(&self, a: &Pointer) -> bool {
        self.equality_graph.bounds_owner_is_root(a)
    }
}
pub(super) fn origins_match<A, W>(
    a: Origins<'_, A, W>,
    b: Origins<'_, A, W>,
    checks: &impl OriginChecks<A, W>,
) -> bool {
    checks.provenance(a.provenance, b.provenance)
        && match (a.bounds, b.bounds) {
            (None, None) if a.known && b.known => true,
            (None, None) if !a.known && !b.known => a
                .opaque
                .zip(b.opaque)
                .is_some_and(|(a, b)| checks.opaque(a, b)),
            (Some((a, aw)), Some((b, bw))) => checks.width(aw, bw) && checks.address(a, b),
            _ => false,
        }
}
pub(super) fn access_match<A, W>(
    required: (&A, Option<&A>),
    available: (&A, Option<&A>, bool),
    checks: &impl OriginChecks<A, W>,
) -> bool {
    checks.provenance(required.0, available.0)
        && required.1.is_none_or(|bounds| match available.1 {
            Some(source) => checks.opaque(bounds, source),
            None => available.2 && checks.opaque_is_root(bounds),
        })
}
/// Only the existing complete-read resolver may supply a stored value. A
/// refusal leaves that side unchanged; both absent results end the attempt.
pub(super) fn complete_match<P>(
    left: &P,
    right: &P,
    mut check: impl FnMut(&P, &P) -> bool,
    mut stored: impl FnMut(&P) -> Option<P>,
) -> bool {
    if check(left, right) {
        return true;
    }
    let a = stored(left);
    let b = stored(right);
    if a.is_none() && b.is_none() {
        return false;
    }
    check(a.as_ref().unwrap_or(left), b.as_ref().unwrap_or(right))
}

fn exact_index(value: &KernelTerm) -> Option<SharedMachineIntegerTerm> {
    let KernelType::Program(ty) = value.ty() else {
        return None;
    };
    let format = MachineIntegerType::from_program_type(*ty)?;
    if matches!(value.node(), crate::kernel::KernelTermNode::Legacy(_))
        && let Some(native) = value.machine_conversion_leaf()
    {
        return Some(SharedMachineIntegerTerm::index(format, native.clone()));
    }
    SharedMachineIntegerTerm::from_shared(format, value.clone())
}

pub(super) fn shared_addresses_equal_with_load_atoms(
    left: &SharedPointerAddress,
    right: &SharedPointerAddress,
    loads: LoadAtomsMatch<'_>,
) -> bool {
    // Borrow block atoms. Exact shared identity skips repeated literal-byte
    // comparisons; distinct producer payloads still use native logical identity.
    let a = &left.node().block;
    let b = &right.node().block;
    if a != b && !pointer_blocks_equal_with_load_atoms(a.native_atom(), b.native_atom(), loads) {
        return false;
    }
    shared_offsets_equal_with_load_atoms(&left.node().offset, &right.node().offset, loads)
}

pub(super) fn shared_offsets_equal_with_load_atoms(
    left: &SharedPointerOffset,
    right: &SharedPointerOffset,
    loads: LoadAtomsMatch<'_>,
) -> bool {
    let mut pending = vec![(left, right)];
    let mut seen: HashSet<(SharedPointerOffset, SharedPointerOffset)> = HashSet::new();
    let mut numeric = HashSet::new();
    let mut exact_indices = HashMap::new();
    let mut index = |value: &KernelTerm| {
        exact_indices
            .entry(value.id())
            .or_insert_with(|| exact_index(value))
            .clone()
    };
    while let Some((a, b)) = pending.pop() {
        crate::instrumentation::record_deterministic_work(1);
        if !seen.insert((a.clone(), b.clone())) {
            continue;
        }
        match (a.node(), b.node()) {
            (O::Add([al, ar]), O::Add([bl, br])) => {
                pending.push((ar, br));
                pending.push((al, bl));
            }
            (O::Constant(a), O::Constant(b)) if a == b => {}
            (O::Variable(a), O::Variable(b)) if a == b => {}
            (
                O::Int32Scaled {
                    value: a,
                    byte_width: aw,
                },
                O::Int32Scaled {
                    value: b,
                    byte_width: bw,
                },
            ) if aw == bw => {
                // Even an identical read root must consult the supplied load
                // authority, exactly as the native Int32Scaled reader does.
                if numeric.insert((a.id(), b.id()))
                    && !operands_equal_with_load_atoms(
                        MachineIntegerType::Int32,
                        V::Shared(a),
                        V::Shared(b),
                        loads,
                    )
                {
                    return false;
                }
            }
            (
                O::Int64Scaled {
                    value: a,
                    byte_width: aw,
                    unsigned: au,
                },
                O::Int64Scaled {
                    value: b,
                    byte_width: bw,
                    unsigned: bu,
                },
            ) if aw == bw && au == bu => {
                // Native wide offsets use exact identity here, not the
                // narrow load-atom rule. Preserve that deliberate boundary.
                if numeric.insert((a.id(), b.id()))
                    && !index(a).zip(index(b)).is_some_and(|(a, b)| a == b)
                {
                    return false;
                }
            }
            _ => return false,
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{KernelTermExport, SubobjectBounds, VerificationSession};
    use std::collections::HashMap;

    // This oracle adapter names only the explicitly selected input addresses.
    // No common tree is exported and no ambient fact/alias set is searched.
    struct Selected<'a> {
        facts: &'a PureFactContext,
        addresses: HashMap<SharedPointerAddress, Pointer>,
        widths: HashMap<KernelTerm, MachineTerm>,
    }
    impl<'a> Selected<'a> {
        fn new(
            facts: &'a PureFactContext,
            values: &[(&PointerValue, &SharedPointerValue)],
        ) -> Self {
            let mut result = Self {
                facts,
                addresses: HashMap::new(),
                widths: HashMap::new(),
            };
            for (native, shared) in values {
                result
                    .addresses
                    .extend(shared.addresses().cloned().zip(native.pointers().cloned()));
                if let Some(e) = native.bounds() {
                    result.widths.insert(
                        shared
                            .node()
                            .qualifiers
                            .as_ref()
                            .unwrap()
                            .bounds
                            .as_ref()
                            .unwrap()
                            .width
                            .clone(),
                        e.width.clone(),
                    );
                }
            }
            result
        }
    }
    impl OriginChecks<SharedPointerAddress, KernelTerm> for Selected<'_> {
        fn provenance(&self, a: &SharedPointerAddress, b: &SharedPointerAddress) -> bool {
            self.facts
                .provenance_equal(&self.addresses[a], &self.addresses[b])
        }
        fn opaque(&self, a: &SharedPointerAddress, b: &SharedPointerAddress) -> bool {
            self.facts
                .bounds_owners_equal(&self.addresses[a], &self.addresses[b])
        }
        fn address(&self, a: &SharedPointerAddress, b: &SharedPointerAddress) -> bool {
            self.facts
                .equality_graph
                .are_equal(&self.addresses[a], &self.addresses[b])
        }
        fn width(&self, a: &KernelTerm, b: &KernelTerm) -> bool {
            self.widths[a] == self.widths[b]
        }
        fn opaque_is_root(&self, a: &SharedPointerAddress) -> bool {
            self.facts
                .equality_graph
                .bounds_owner_is_root(&self.addresses[a])
        }
    }

    #[test]
    fn shared_load_atom_equality_keeps_narrow_and_wide_native_policies() {
        let _session = VerificationSession::enter();
        let cell = SymbolicMemory::global_pointer("shared-check-index");
        let before = SymbolicMemory::new().with_block("shared-check-index", 16);
        let after = before
            .clone()
            .store(cell.clone(), ProgramValue::Int32(MachineTerm::constant(9)));
        for format in [
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ] {
            let make = |memory| {
                let value = SharedMachineIntegerTerm::index(
                    format,
                    MachineTerm::MemoryLoad(
                        ProgramPoint::at(&(crate::kernel::intern_memory(memory))),
                        Box::new(cell.clone()),
                        if matches!(
                            format,
                            MachineIntegerType::Int32 | MachineIntegerType::UInt32
                        ) {
                            LoadKind::Int32
                        } else {
                            LoadKind::Bits64
                        },
                    ),
                );
                Pointer {
                    block: PointerBlock::Concrete("shared-check-base".into()),
                    offset: if matches!(
                        format,
                        MachineIntegerType::Int32 | MachineIntegerType::UInt32
                    ) {
                        PointerOffsetTerm::Int32Scaled {
                            value,
                            byte_width: 4,
                        }
                    } else {
                        PointerOffsetTerm::Int64Scaled {
                            value,
                            byte_width: 8,
                            unsigned: true,
                        }
                    },
                }
            };
            let a = make(before.clone());
            let b = make(after.clone());
            for right in [&a, &b] {
                let sa = SharedPointerAddress::import(&a);
                let sb = SharedPointerAddress::import(right);
                for allowed in [false, true] {
                    let loads = |_: &MachineTerm, _: &MachineTerm| allowed;
                    let expected = pointers_equal_with_load_atoms(&a, right, &loads);
                    let exports = KernelTermExport::machine_export_count();
                    assert_eq!(
                        shared_addresses_equal_with_load_atoms(&sa, &sb, &loads),
                        expected,
                        "{format:?}, allowed={allowed}"
                    );
                    assert_eq!(KernelTermExport::machine_export_count(), exports);
                }
            }
        }
    }
    #[test]
    fn shared_loaded_blocks_use_the_existing_selected_load_authority() {
        let _session = VerificationSession::enter();
        let cell = Pointer::symbolic(Variable(1012050));
        let before = crate::kernel::intern_memory(SymbolicMemory::new());
        let after = crate::kernel::intern_memory(SymbolicMemory::new().with_block("different", 8));
        let a = SharedPointerAddress::import(&Pointer::loaded_value(&before, &cell));
        let b = SharedPointerAddress::import(&Pointer::loaded_value(&after, &cell));
        assert!(shared_addresses_equal_with_load_atoms(&a, &a, &|_, _| {
            false
        }));
        assert!(!shared_addresses_equal_with_load_atoms(&a, &b, &|_, _| {
            false
        }));
        assert!(shared_addresses_equal_with_load_atoms(&a, &b, &|_, _| true));
    }
    #[test]
    fn shared_origins_require_the_same_bounds_start_and_width_evidence() {
        let _session = VerificationSession::enter();
        let a = Pointer::symbolic(Variable(1012000));
        let b = Pointer::symbolic(Variable(1012001));
        let provenance = std::sync::Arc::new(Pointer::symbolic(Variable(1012002)));
        let make = |start, width| {
            PointerValue::new(a.clone(), ProgramType::Int32Pointer)
                .with_provenance(provenance.clone())
                .with_bounds(Some(SubobjectBounds {
                    start,
                    width: MachineTerm::constant(width),
                }))
        };
        let left = make(a.clone(), 4);
        let right = make(b.clone(), 4);
        let wrong_width = make(b.clone(), 8);
        let sl = SharedPointerValue::import(&left);
        let sr = SharedPointerValue::import(&right);
        let sw = SharedPointerValue::import(&wrong_width);
        let before = PureFactContext::new();
        let after = before
            .clone()
            .assume_condition(ConditionTerm::pointer_equal(a, b), true);
        for (facts, expected) in [(&before, false), (&after, true)] {
            let selected =
                Selected::new(facts, &[(&left, &sl), (&right, &sr), (&wrong_width, &sw)]);
            let exports = KernelTermExport::machine_export_count();
            assert_eq!(
                origins_match(Origins::shared(&sl), Origins::shared(&sr), &selected),
                expected
            );
            assert_eq!(facts.pointer_provenance_match(&left, &right), expected);
            assert!(!origins_match(
                Origins::shared(&sl),
                Origins::shared(&sw),
                &selected
            ));
            assert_eq!(KernelTermExport::machine_export_count(), exports);
        }
    }
    #[test]
    fn shared_access_keeps_complete_value_and_root_bounds_authority() {
        let _session = VerificationSession::enter();
        let memory = crate::kernel::intern_memory(SymbolicMemory::new());
        let cell = Pointer::symbolic(Variable(1012100));
        let read = PointerValue::from_read(
            Pointer::loaded_value(&memory, &cell),
            ProgramType::Int32Pointer,
            &memory,
            &cell,
        );
        let base = Pointer {
            block: PointerBlock::Heap(1012101),
            offset: PointerOffsetTerm::Constant(0),
        };
        let stored = PointerValue::new(base.clone(), ProgramType::Int32Pointer);
        let bounded = stored.clone().with_bounds(Some(SubobjectBounds {
            start: base.clone(),
            width: MachineTerm::constant(4),
        }));
        let held = MemoryRange::new(base.clone(), 0u32.into(), 8u32.into());
        let before = PureFactContext::new().assume_condition(
            ConditionTerm::pointer_equal(read.pointer().clone(), base),
            true,
        );
        let after = before.clone().assume_condition(
            ConditionTerm::pointer_value_equal(read.clone(), stored.clone()),
            true,
        );
        let bounded_facts = before.clone().assume_condition(
            ConditionTerm::pointer_value_equal(read.clone(), bounded.clone()),
            true,
        );
        let sr = SharedPointerValue::import(&read);
        let ss = SharedPointerValue::import(&stored);
        let sb = SharedPointerValue::import(&bounded);
        let available = SharedPointerAddress::import(&held.provenance);
        for (facts, expected) in [(&before, false), (&after, true), (&bounded_facts, false)] {
            let selected = Selected::new(facts, &[(&read, &sr), (&stored, &ss), (&bounded, &sb)]);
            let origin = Origins::shared(&sr);
            let exports = KernelTermExport::machine_export_count();
            assert_eq!(
                access_match(
                    (origin.provenance, origin.opaque),
                    (&available, None, true),
                    &selected
                ),
                expected
            );
            assert_eq!(
                facts.access_provenance_match(read.access_provenance(), &held),
                expected
            );
            assert_eq!(KernelTermExport::machine_export_count(), exports);
        }
    }
}
#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/assumptions/pointer_checks.rs");
}
