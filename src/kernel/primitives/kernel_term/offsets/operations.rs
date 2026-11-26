//! Readers and reconstruction for retained offset conditions. These preserve
//! native offset policy; the bounded residue test keeps its existing limits.
use super::*;

impl KernelAddressOffset {
    pub(super) fn constant_value(&self) -> Option<i64> {
        match self {
            Self::Constant(value) => Some(*value),
            Self::Variable(_) => None,
            Self::Add([a, b]) => a.as_const()?.checked_add(b.as_const()?),
            Self::Int32Scaled { value, byte_width } => {
                (MachineOperandView::Shared(value).word32_constant()? as i32 as i64)
                    .checked_mul(*byte_width)
            }
            Self::Int64Scaled {
                value,
                byte_width,
                unsigned,
            } => {
                let value = MachineOperandView::Shared(value);
                let value = if *unsigned {
                    i64::try_from(value.uint64_constant()?).ok()?
                } else {
                    value.int64_constant()?
                };
                value.checked_mul(*byte_width)
            }
        }
    }
}

impl SharedAddressOffset {
    pub(crate) fn as_const(&self) -> Option<i64> {
        self.0.constant
    }

    pub(crate) fn add(mut left: Self, mut right: Self) -> Self {
        loop {
            crate::instrumentation::record_deterministic_work(1);
            if let (Some(a), Some(b)) = (left.as_const(), right.as_const()) {
                return KernelAddressOffset::Constant(a + b).into_shared().unwrap();
            }
            if left.as_const() == Some(0) {
                return right;
            }
            if right.as_const() == Some(0) {
                return left;
            }
            if let (KernelAddressOffset::Add([base, trailing]), KernelAddressOffset::Constant(b)) =
                (left.node(), right.node())
                && let Some(a) = trailing.as_const()
            {
                right = KernelAddressOffset::Constant(a + b).into_shared().unwrap();
                left = base.clone();
                continue;
            }
            return KernelAddressOffset::Add([left, right])
                .into_shared()
                .unwrap();
        }
    }

    /// A fixed input pair shares one traversal. The callback selects raw or
    /// smart reconstruction and the caller's lexical/state rewrite policy.
    pub(crate) fn try_map_pair<E>(
        roots: &[Self; 2],
        map: impl FnMut(&Self, KernelAddressOffset) -> Result<Self, E>,
    ) -> Result<[Self; 2], E> {
        Self::try_map_roots(roots, |_| None, map)
    }

    pub(crate) fn try_map_root<E>(
        &self,
        map: impl FnMut(&Self, KernelAddressOffset) -> Result<Self, E>,
    ) -> Result<Self, E> {
        self.try_map_root_replacing(|_| None, map)
    }

    /// Replace selected subtrees before visiting their children.
    pub(crate) fn try_map_root_replacing<E>(
        &self,
        replace: impl FnMut(&Self) -> Option<Self>,
        map: impl FnMut(&Self, KernelAddressOffset) -> Result<Self, E>,
    ) -> Result<Self, E> {
        let [root] = Self::try_map_roots(std::array::from_ref(self), replace, map)?;
        Ok(root)
    }

    fn try_map_roots<E, const N: usize>(
        roots: &[Self; N],
        mut replace: impl FnMut(&Self) -> Option<Self>,
        mut map: impl FnMut(&Self, KernelAddressOffset) -> Result<Self, E>,
    ) -> Result<[Self; N], E> {
        let mut results: HashMap<SharedAddressOffset, SharedAddressOffset> = HashMap::new();
        let mut pending: Vec<_> = roots.iter().rev().map(|root| (root, false)).collect();
        while let Some((root, finish)) = pending.pop() {
            if results.contains_key(root) {
                continue;
            }
            crate::instrumentation::record_deterministic_work(1);
            if !finish && let Some(replacement) = replace(root) {
                results.insert(root.clone(), replacement);
                continue;
            }
            let node = match root.node() {
                KernelAddressOffset::Add([a, b]) => {
                    if !finish {
                        pending.extend([(root, true), (b, false), (a, false)]);
                        continue;
                    }
                    KernelAddressOffset::Add([results[a].clone(), results[b].clone()])
                }
                node => node.clone(),
            };
            results.insert(root.clone(), map(root, node)?);
        }
        Ok(roots.each_ref().map(|root| results[root].clone()))
    }

    pub(crate) fn visit_pair(roots: &[Self; 2], visit: impl FnMut(&KernelAddressOffset)) {
        Self::visit_pair_in_order(roots, false, visit);
    }

    /// Resource-read collection historically visits each Add right-first;
    /// variable and state readers use left-first. Preserve the caller's order.
    pub(crate) fn visit_pair_in_order(
        roots: &[Self; 2],
        right_first: bool,
        visit: impl FnMut(&KernelAddressOffset),
    ) {
        Self::visit_roots(roots, right_first, visit);
    }

    pub(crate) fn visit_root_in_order(
        &self,
        right_first: bool,
        visit: impl FnMut(&KernelAddressOffset),
    ) {
        Self::visit_roots(std::slice::from_ref(self), right_first, visit);
    }

    fn visit_roots(roots: &[Self], right_first: bool, mut visit: impl FnMut(&KernelAddressOffset)) {
        Self::visit_roots_while(roots, right_first, |node| {
            visit(node);
            true
        });
    }

    pub(crate) fn visit_root_while(&self, visit: impl FnMut(&KernelAddressOffset) -> bool) -> bool {
        Self::visit_roots_while(std::slice::from_ref(self), false, visit)
    }

    fn visit_roots_while(
        roots: &[Self],
        right_first: bool,
        mut visit: impl FnMut(&KernelAddressOffset) -> bool,
    ) -> bool {
        let mut pending: Vec<_> = roots.iter().rev().collect();
        let mut seen = std::collections::HashSet::new();
        while let Some(root) = pending.pop() {
            if !seen.insert(root) {
                continue;
            }
            crate::instrumentation::record_deterministic_work(1);
            if !visit(root.node()) {
                return false;
            }
            if right_first {
                pending.extend(root.node().offset_children());
            } else {
                pending.extend(root.node().offset_children().iter().rev());
            }
        }
        true
    }

    pub(crate) fn syntax_equal(&self, other: &Self) -> bool {
        let mut pending = vec![(self, other)];
        let mut seen = std::collections::HashSet::new();
        while let Some((a, b)) = pending.pop() {
            if a == b || !seen.insert((a, b)) {
                continue;
            }
            crate::instrumentation::record_deterministic_work(1);
            match (a.node(), b.node()) {
                (KernelAddressOffset::Constant(a), KernelAddressOffset::Constant(b)) if a == b => {}
                (KernelAddressOffset::Variable(a), KernelAddressOffset::Variable(b)) if a == b => {}
                (KernelAddressOffset::Add(a), KernelAddressOffset::Add(b)) => {
                    pending.extend(a.iter().zip(b))
                }
                (
                    KernelAddressOffset::Int32Scaled {
                        value: a,
                        byte_width: aw,
                    },
                    KernelAddressOffset::Int32Scaled {
                        value: b,
                        byte_width: bw,
                    },
                ) if aw == bw => {
                    if Self::exact_index(a) != Self::exact_index(b) {
                        return false;
                    }
                }
                (
                    KernelAddressOffset::Int64Scaled {
                        value: a,
                        byte_width: aw,
                        unsigned: au,
                    },
                    KernelAddressOffset::Int64Scaled {
                        value: b,
                        byte_width: bw,
                        unsigned: bu,
                    },
                ) if aw == bw && au == bu => {
                    if Self::exact_index(a) != Self::exact_index(b) {
                        return false;
                    }
                }
                _ => return false,
            }
        }
        true
    }

    pub(crate) fn exact_index(root: &KernelTerm) -> SharedMachineIntegerTerm {
        let KernelType::Program(ty) = root.ty() else {
            unreachable!("typed offset index")
        };
        let format = MachineIntegerType::from_program_type(*ty).expect("numeric offset index");
        if let Some(index) = root.retained_address_index(format) {
            return index.clone();
        }
        if let Some(native) = root.retained_machine_input() {
            return SharedMachineIntegerTerm::index(format, native.clone());
        }
        SharedMachineIntegerTerm::from_shared(format, root.clone())
            .expect("typed shared offset index")
    }

    fn residue_summary(&self) -> Option<(u64, i64)> {
        let mut pending = vec![self];
        let mut count = 0;
        let mut divisor = 0;
        let mut constant = 0;
        while let Some(root) = pending.pop() {
            // Count occurrences, including Add nodes, exactly as the native
            // bounded classifier does. Sharing must not widen its admission.
            count += 1;
            crate::instrumentation::record_deterministic_work(1);
            if count > 64 {
                return None;
            }
            match root.node() {
                KernelAddressOffset::Add([a, b]) => pending.extend([b, a]),
                KernelAddressOffset::Constant(value) if value.unsigned_abs() < (1u64 << 48) => {
                    constant += value
                }
                KernelAddressOffset::Int32Scaled { byte_width, .. }
                    if byte_width.unsigned_abs() <= (1u64 << 24) =>
                {
                    divisor = gcd(divisor, byte_width.unsigned_abs())
                }
                _ => return None,
            }
        }
        Some((divisor, constant))
    }
}
fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}
impl KernelTerm {
    pub(crate) fn address_offset_equal_raw(arguments: [SharedAddressOffset; 2]) -> Self {
        Self::intern(
            KernelType::Bool,
            KernelTermNode::AddressOffsetEqual { arguments },
        )
    }
    pub(crate) fn address_offset_equal(arguments: [SharedAddressOffset; 2]) -> Self {
        let [a, b] = &arguments;
        let constant = match (a.as_const(), b.as_const()) {
            (Some(a), Some(b)) => Some(a == b),
            _ => match (a.residue_summary(), b.residue_summary()) {
                (Some((ad, ac)), Some((bd, bc)))
                    if gcd(ad, bd) > 1 && (ac - bc).unsigned_abs() % gcd(ad, bd) != 0 =>
                {
                    Some(false)
                }
                _ => None,
            },
        };
        match constant {
            Some(value) => Self::intern(KernelType::Bool, KernelTermNode::BoolLiteral(value)),
            None => Self::address_offset_equal_raw(arguments),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::BooleanOperandView as B;

    fn sources() -> Vec<AddressOffset> {
        let mut result = vec![
            AddressOffset::constant(0),
            AddressOffset::constant(1),
            AddressOffset::constant(i64::MAX),
            AddressOffset::variable(Variable(998001)),
        ];
        for width in [0, -8, 4, 1 << 24, (1 << 24) + 1] {
            for bits in [
                OldMachineTerm::constant(0),
                OldMachineTerm::Variable(Variable(998002)),
            ] {
                result.push(AddressOffset::scaled_int32_node(bits, width));
            }
            for unsigned in [false, true] {
                result.push(AddressOffset::scaled_int64_node(
                    OldMachineTerm::Variable(Variable(998003)),
                    width,
                    unsigned,
                ));
            }
        }
        for n in [30, 31, 32, 33] {
            let mut offset =
                AddressOffset::scaled_int32_node(OldMachineTerm::Variable(Variable(998002)), 4);
            for _ in 0..n {
                offset = AddressOffset::raw_add(offset, AddressOffset::constant(1));
            }
            result.push(offset);
        }
        result
    }

    #[test]
    fn offset_condition_constructors_preserve_native_reductions_and_residue_limits() {
        let _session = crate::kernel::VerificationSession::enter();
        let values = sources();
        for a in &values {
            let shared = a.shared().clone();
            assert_eq!(shared.as_const(), a.as_const());
            for b in &values {
                let root = KernelTerm::address_offset_equal([shared.clone(), b.shared().clone()]);
                let expected = OldConditionTerm::address_offset_equal(a.clone(), b.clone());
                assert_eq!(
                    KernelTermExport::condition(&root).unwrap(),
                    expected,
                    "a={a:?}, b={b:?}"
                );
            }
        }
    }

    #[test]
    fn offset_conditions_keep_raw_shape_and_substitution_policy() {
        let _session = crate::kernel::VerificationSession::enter();
        for offset in sources() {
            let source = OldConditionTerm::AddressOffsetEqual(
                Box::new(AddressOffset::raw_add(AddressOffset::constant(0), offset)),
                Box::new(AddressOffset::constant(5)),
            );
            let root = KernelTermImport::default().condition(&source);
            assert!(matches!(
                root.node(),
                KernelTermNode::AddressOffsetEqual { .. }
            ));
            assert_eq!(
                format!("{:?}", KernelTermExport::condition(&root).unwrap()),
                format!("{source:?}")
            );
            assert!(B::Shared(&root).syntax_equal(B::Native(&source)));
            for from in [Variable(998002), Variable(998099)] {
                let to = OldMachineTerm::constant(3);
                let native = crate::kernel::reasoning::substitute_bitvector_variable_in_condition(
                    &source, from, &to,
                );
                let shared =
                    crate::kernel::reasoning::substitute_bitvector_variable_in_common_condition(
                        &root, from, &to,
                    )
                    .unwrap();
                assert_eq!(
                    format!("{:?}", KernelTermExport::condition(&shared).unwrap()),
                    format!("{native:?}")
                );
            }
            let pointer = Address::symbolic(Variable(998100));
            assert_eq!(
                crate::kernel::reasoning::substitute_pointer_variable_in_common_condition(
                    &root,
                    Variable(998001),
                    &pointer
                ),
                Some(root)
            );
        }
    }

    #[test]
    fn offset_conditions_preserve_narrow_load_authority_and_wide_exact_identity() {
        let _session = crate::kernel::VerificationSession::enter();
        let before = crate::kernel::SymbolicMemory::new()
            .with_block("offset-condition", 8)
            .with_block("offset-other", 4);
        let after = before.clone().store(
            crate::kernel::SymbolicMemory::global_pointer("offset-other"),
            ProgramValue::Int32(OldMachineTerm::constant(1)),
        );
        let memory_a = crate::kernel::intern_memory(before);
        let memory_b = crate::kernel::intern_memory(after);
        for wide in [false, true] {
            let condition = |memory| {
                let value = OldMachineTerm::read_named(
                    memory,
                    Box::new(crate::kernel::SymbolicMemory::global_pointer(
                        "offset-condition",
                    )),
                    if wide {
                        LoadKind::Bits64
                    } else {
                        LoadKind::Int32
                    },
                );
                let offset = if wide {
                    AddressOffset::scaled_int64_node(value, 8, false)
                } else {
                    AddressOffset::scaled_int32_node(value, 4)
                };
                OldConditionTerm::AddressOffsetEqual(
                    Box::new(offset),
                    Box::new(AddressOffset::constant(0)),
                )
            };
            let a = condition(ProgramPoint::at(&memory_a));
            let b = condition(ProgramPoint::at(&memory_b));
            let ar = KernelTermImport::default().condition(&a);
            let br = KernelTermImport::default().condition(&b);
            for allowed in [false, true] {
                let loads = |_: &OldMachineTerm, _: &OldMachineTerm| allowed;
                let expected =
                    crate::kernel::assumptions::conditions_equal_with_load_atoms(&a, &b, &loads);
                assert_eq!(
                    crate::kernel::assumptions::boolean_operands_equal_with_load_atoms(
                        B::Shared(&ar),
                        B::Shared(&br),
                        &loads
                    ),
                    expected
                );
                assert_eq!(
                    crate::kernel::assumptions::boolean_operands_equal_with_load_atoms(
                        B::Shared(&ar),
                        B::Native(&b),
                        &loads
                    ),
                    expected
                );
                assert!(
                    crate::kernel::assumptions::boolean_operands_equal_with_load_atoms(
                        B::Shared(&ar),
                        B::Shared(&ar),
                        &loads
                    )
                );
            }
        }
    }
}

#[cfg(test)]
mod identity_tests {
    use super::*;
    #[test]
    fn offset_condition_identity_preserves_native_annotation_policy() {
        use crate::kernel::effective_type::{CAccessClass, CScalarClass};
        let _session = crate::kernel::VerificationSession::enter();
        let sources = [CScalarClass::Int, CScalarClass::Char].map(|class| {
            OldConditionTerm::AddressOffsetEqual(
                Box::new(AddressOffset::scaled_int64_node(
                    OldMachineTerm::IntegerAddress(
                        Box::new(Address::symbolic(Variable(998400))),
                        crate::kernel::AddressObjectClass::new(Some(CAccessClass::Scalar(class))),
                    ),
                    1,
                    true,
                )),
                Box::new(AddressOffset::constant(0)),
            )
        });
        let roots = sources
            .each_ref()
            .map(|source| KernelTermImport::default().condition(source));
        assert_eq!(sources[0], sources[1]);
        assert_ne!(roots[0], roots[1]);
        assert!(
            BooleanOperandView::Shared(&roots[0])
                .syntax_equal(BooleanOperandView::Shared(&roots[1]))
        );
        for source in &sources {
            let source = OldConditionTerm::BoolEqual(
                Box::new(source.clone()),
                Box::new(OldConditionTerm::Constant(false)),
            );
            let root = KernelTermImport::default().condition(&source);
            let target = Address::symbolic(Variable(998401));
            let expected = crate::kernel::proof::term_rewrite::TermRewrite::for_pointer_variable(
                Variable(998400),
                &target,
            )
            .condition(&source);
            let actual = crate::kernel::reasoning::substitute_pointer_variable_in_common_condition(
                &root,
                Variable(998400),
                &target,
            )
            .unwrap();
            assert_eq!(
                format!("{:?}", KernelTermExport::condition(&actual).unwrap()),
                format!("{expected:?}")
            );
        }
        for (root, source) in roots.iter().zip(&sources) {
            assert_eq!(
                format!("{:?}", KernelTermExport::condition(root).unwrap()),
                format!("{source:?}")
            );
        }
    }
}
