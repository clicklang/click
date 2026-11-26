//! Allocation-independent written syntax at the certification boundary.
//! No arithmetic observation, fact lookup, or read resolution. Selected native
//! adapters preserve the existing certification admission policy.
use super::*;
use crate::kernel::{KernelTermNode as N, PureFunctionArgument as A};
use std::collections::HashSet;
mod pointers;

#[derive(Clone, Copy)]
enum CallArgument<'a> {
    Native(&'a A),
    Shared(&'a KernelTerm),
    Scalar(ProgramType, &'a OldMachineTerm),
}

impl<'a> CallArgument<'a> {
    fn retained(self) -> Self {
        let Self::Shared(root) = self else {
            return self;
        };
        match root.node() {
            N::ObservedPointer(value) => Self::Shared(value.source()).retained(),
            N::ImportedScalar(input) => Self::Scalar(input.carrier(), input.value()),
            _ => root.written_argument().map_or(self, Self::Native),
        }
    }

    fn scalar_operand(self) -> Option<(ProgramType, Operand<'a>)> {
        match self {
            Self::Scalar(ty, word) => Some((ty, Operand::Old(word))),
            Self::Native(A::Value(value)) => {
                Some((value.program_type(), Operand::Old(scalar(value)?)))
            }
            Self::Native(A::SharedMachine(value)) => {
                Some((value.ty().program_type(), value.operand_view()))
            }
            Self::Shared(root) => match root.ty() {
                KernelType::Program(ty)
                    if MachineIntegerType::from_program_type(*ty).is_some()
                        || crate::kernel::KernelFloatType::from_program_type(*ty).is_some() =>
                {
                    Some((*ty, Operand::Shared(root)))
                }
                _ => None,
            },
            _ => None,
        }
    }
}

fn scalar(value: &ProgramValue) -> Option<&OldMachineTerm> {
    match value {
        crate::kernel::integer_c_value!(term)
        | ProgramValue::Bool(term)
        | ProgramValue::Float32(term)
        | ProgramValue::Float64(term) => Some(term),
        _ => None,
    }
}

#[derive(Default)]
struct Comparison {
    seen: HashSet<(u64, u64)>,
}

pub(super) fn conditions_equal(left: &OldConditionTerm, right: &OldConditionTerm) -> bool {
    Comparison::default().condition(left, right)
}

pub(super) fn algebraic_equal(left: &AlgebraicTerm, right: &AlgebraicTerm) -> bool {
    Comparison::default().algebraic(left, right)
}

pub(super) fn stored_algebraic_equal(
    left: &StoredAlgebraicTerm,
    right: &StoredAlgebraicTerm,
) -> bool {
    let mut comparison = Comparison::default();
    match (left.root(), right.root()) {
        (Some(left), Some(right)) => comparison.common_algebraic(left, right),
        (Some(left), None) => comparison.mixed_algebraic(left, right.old_form()),
        (None, Some(right)) => comparison.mixed_algebraic(right, left.old_form()),
        (None, None) => algebraic_equal(left.old_form(), right.old_form()),
    }
}

impl Comparison {
    fn algebraic(&mut self, left: &AlgebraicTerm, right: &AlgebraicTerm) -> bool {
        use crate::kernel::AlgebraicTermNode as T;
        crate::instrumentation::record_deterministic_work(1);
        if left.algebraic_type != right.algebraic_type {
            return false;
        }
        match (&left.node, &right.node) {
            (T::Variable(a), T::Variable(b)) => a == b,
            (
                T::PureFunctionApplication {
                    name: an,
                    arguments: aa,
                },
                T::PureFunctionApplication {
                    name: bn,
                    arguments: ba,
                },
            ) => {
                an == bn
                    && aa.len() == ba.len()
                    && aa.iter().zip(ba).all(|(a, b)| self.argument(a, b))
            }
            (
                T::MemoryLoad {
                    point: am,
                    pointer: ap,
                },
                T::MemoryLoad {
                    point: bm,
                    pointer: bp,
                },
            ) => am.read_key() == bm.read_key() && self.pointer(ap, bp),
            // Match/conditional/constructor payloads keep their existing
            // certification route. This boundary admits only call syntax.
            _ => false,
        }
    }
    fn condition(&mut self, left: &OldConditionTerm, right: &OldConditionTerm) -> bool {
        use OldConditionTerm as C;
        crate::instrumentation::record_deterministic_work(1);
        match (left, right) {
            (
                C::Compare {
                    format: a,
                    relation: ar,
                    left: al,
                    right: av,
                },
                C::Compare {
                    format: b,
                    relation: br,
                    left: bl,
                    right: bv,
                },
            ) => {
                a == b
                    && ar == br
                    && self.machine(Operand::Old(al), Operand::Old(bl))
                    && self.machine(Operand::Old(av), Operand::Old(bv))
            }
            (C::Constant(a), C::Constant(b)) => a == b,
            (C::Variable(a), C::Variable(b)) => a == b,
            // Other logical domains retain the existing certification route.
            _ => false,
        }
    }

    fn machine(&mut self, left: Operand<'_>, right: Operand<'_>) -> bool {
        let mut pending = vec![(left, right)];
        while let Some((left, right)) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            if let (Operand::Shared(a), Operand::Shared(b)) = (left, right) {
                if a.ty() != b.ty() {
                    return false;
                }
                if a == b || !self.seen.insert((a.id(), b.id())) {
                    continue;
                }
                if let (N::MachineIf { arguments: a }, N::MachineIf { arguments: b }) =
                    (a.node(), b.node())
                {
                    // Retain exact guard identity; do not export a logical DAG.
                    if a[0] != b[0] {
                        return false;
                    }
                    pending.extend([
                        (Operand::Shared(&a[1]), Operand::Shared(&b[1])),
                        (Operand::Shared(&a[2]), Operand::Shared(&b[2])),
                    ]);
                    continue;
                }
            }
            if matches!(left, Operand::Shared(root) if matches!(root.node(), N::FloatConvert { .. }))
                || matches!(right, Operand::Shared(root) if matches!(root.node(), N::FloatConvert { .. }))
            {
                let (Some((a, av)), Some((b, bv))) =
                    (numeric_conversion(left), numeric_conversion(right))
                else {
                    return false;
                };
                if a != b {
                    return false;
                }
                pending.push((av, bv));
                continue;
            }
            // Common machine calls use the same argument reader as retained
            // float calls. Do not build a native call merely to compare it.
            let retained_call = |view| {
                matches!(view, Operand::Shared(root)
                if matches!(root.node(), N::FloatCall(_))
                    || matches!(root.node(), N::Call { .. })
                        && matches!(root.ty(), KernelType::Program(ty)
                            if MachineIntegerType::from_program_type(*ty).is_some()))
            };
            if retained_call(left) || retained_call(right) {
                let (Some((an, aa)), Some((bn, ba))) = (numeric_call(left), numeric_call(right))
                else {
                    return false;
                };
                if an != bn
                    || aa.len() != ba.len()
                    || !aa
                        .into_iter()
                        .zip(ba)
                        .all(|(a, b)| self.call_argument(a, b))
                {
                    return false;
                }
                continue;
            }
            // Native Integer-to-machine syntax is not admitted by this
            // comparison route. Keep that refusal without exporting its Integer
            // operand; the shared/shared identity shortcut above is unchanged.
            if [left, right].into_iter().any(|view| {
                matches!(view, Operand::Shared(root) if matches!(root.node(), N::IntegerToMachine { .. }))
            }) {
                return false;
            }
            // Float atoms have a bounded native reading. Compound float syntax
            // keeps the native certification refusal until its own reader moves.
            let atom = |view| match view {
                Operand::Shared(root)
                    if crate::kernel::FloatOperandView::from_shared(root).is_some() =>
                {
                    crate::kernel::FloatOperandView::from_shared(root)?
                        .old_form()
                        .map(Operand::Old)
                }
                view => Some(view),
            };
            let (Some(left), Some(right)) = (atom(left), atom(right)) else {
                return false;
            };
            if let (Some((af, ao, [al, ar])), Some((bf, bo, [bl, br]))) =
                (left.binary(), right.binary())
            {
                if af != bf || ao != bo {
                    return false;
                }
                pending.extend([(al, bl), (ar, br)]);
                continue;
            }
            if let (Some((ae, af, at, a)), Some((be, bf, bt, b))) = (left.cast(), right.cast()) {
                if (ae, af, at) != (be, bf, bt) {
                    return false;
                }
                pending.push((a, b));
                continue;
            }
            if let (Some((af, ao, a)), Some((bf, bo, b))) = (left.unary(), right.unary()) {
                if (af, ao) != (bf, bo) {
                    return false;
                }
                pending.push((a, b));
                continue;
            }
            if let (Some(a), Some(b)) = (left.literal(), right.literal()) {
                if a != b {
                    return false;
                }
                continue;
            }
            if let (Some(a), Some(b)) = (left.variable(), right.variable()) {
                if a != b {
                    return false;
                }
                continue;
            }
            if left.fold().is_some()
                || right.fold().is_some()
                || left.matched().is_some()
                || right.matched().is_some()
            {
                if !crate::kernel::machine_operand_syntax_cmp(left, right).is_eq() {
                    return false;
                }
                continue;
            }
            // Selected native leaves are already stored payloads, not exports.
            fn native(view: Operand<'_>) -> Option<&OldMachineTerm> {
                match view {
                    Operand::Old(term) => Some(term),
                    Operand::Shared(root) => root
                        .machine_conversion_leaf()
                        .or_else(|| root.machine_read_leaf()),
                }
            }
            let (Some(a), Some(b)) = (native(left), native(right)) else {
                return false;
            };
            match (a, b) {
                (
                    OldMachineTerm::ClickFunctionApplication {
                        name: an,
                        arguments: aa,
                    },
                    OldMachineTerm::ClickFunctionApplication {
                        name: bn,
                        arguments: ba,
                    },
                ) => {
                    if an != bn
                        || aa.len() != ba.len()
                        || !aa.iter().zip(ba).all(|(a, b)| self.argument(a, b))
                    {
                        return false;
                    }
                }
                (
                    OldMachineTerm::PureFunctionApplication {
                        name: an,
                        arguments: aa,
                    },
                    OldMachineTerm::PureFunctionApplication {
                        name: bn,
                        arguments: ba,
                    },
                ) => {
                    if an != bn || aa.len() != ba.len() {
                        return false;
                    }
                    pending.extend(
                        aa.iter()
                            .zip(ba)
                            .map(|(a, b)| (Operand::Old(a), Operand::Old(b))),
                    );
                }
                (
                    OldMachineTerm::If {
                        condition: ac,
                        then_term: at,
                        else_term: ae,
                    },
                    OldMachineTerm::If {
                        condition: bc,
                        then_term: bt,
                        else_term: be,
                    },
                ) => {
                    if !self.condition(ac, bc) {
                        return false;
                    }
                    pending.extend([
                        (Operand::Old(at), Operand::Old(bt)),
                        (Operand::Old(ae), Operand::Old(be)),
                    ]);
                }
                (
                    OldMachineTerm::MemoryLoad(am, ap, ak),
                    OldMachineTerm::MemoryLoad(bm, bp, bk),
                ) => {
                    if am.read_version_id() != bm.read_version_id()
                        || am.shared_memory().arena_id() != bm.shared_memory().arena_id()
                        || ak != bk
                        || !self.pointer(ap, bp)
                    {
                        return false;
                    }
                }
                // Unknown native domains are not granted a new equivalence.
                _ => return false,
            }
        }
        true
    }

    fn call_argument(&mut self, left: CallArgument<'_>, right: CallArgument<'_>) -> bool {
        use CallArgument::{Native, Scalar, Shared};
        let (left, right) = (left.retained(), right.retained());
        // Only literals and raw C Boolean variables have an admitted word
        // reading here. Other logical roots become native BoolCast syntax,
        // which this route refuses; do not export their condition to refuse it.
        if let Shared(root) = left
            && matches!(
                root.ty(),
                KernelType::Bool | KernelType::Program(ProgramType::Bool)
            )
        {
            let Some(word) = boolean_argument_word(root) else {
                return false;
            };
            return self.call_argument(Scalar(ProgramType::Bool, &word), right);
        }
        if let Shared(root) = right
            && matches!(
                root.ty(),
                KernelType::Bool | KernelType::Program(ProgramType::Bool)
            )
        {
            let Some(word) = boolean_argument_word(root) else {
                return false;
            };
            return self.call_argument(left, Scalar(ProgramType::Bool, &word));
        }
        if let Some(equal) = self.pointer_arguments(left, right) {
            return equal;
        }
        match (left, right) {
            (Scalar(..), _) | (_, Scalar(..)) => {
                let (Some((a_type, a)), Some((b_type, b))) =
                    (left.scalar_operand(), right.scalar_operand())
                else {
                    return false;
                };
                a_type == b_type && self.machine(a, b)
            }
            (Native(a), Native(b)) => self.argument(a, b),
            (Shared(a), Shared(b)) if matches!(a.ty(), KernelType::Algebraic(_)) => {
                self.common_algebraic(a, b)
            }
            (Shared(a), Native(A::Algebraic(b))) | (Native(A::Algebraic(b)), Shared(a)) => {
                self.mixed_algebraic(a, b)
            }
            (Shared(a), Shared(b))
                if a.ty() == b.ty()
                    && matches!(a.ty(), KernelType::Program(ty) if MachineIntegerType::from_program_type(*ty).is_some() || crate::kernel::KernelFloatType::from_program_type(*ty).is_some()) =>
            {
                self.machine(Operand::Shared(a), Operand::Shared(b))
            }
            (Shared(a), Native(A::SharedMachine(b))) | (Native(A::SharedMachine(b)), Shared(a)) => {
                a.ty() == &KernelType::Program(b.ty().program_type())
                    && self.machine(Operand::Shared(a), b.operand_view())
            }
            (Shared(a), Native(A::Value(b))) | (Native(A::Value(b)), Shared(a))
                if a.ty() == &KernelType::Program(b.program_type()) =>
            {
                match b {
                    crate::kernel::integer_c_value!(bits)
                    | ProgramValue::Float32(bits)
                    | ProgramValue::Float64(bits) => {
                        self.machine(Operand::Shared(a), Operand::Old(bits))
                    }
                    _ => false,
                }
            }
            _ => false,
        }
    }

    fn mixed_algebraic(&mut self, shared: &KernelTerm, native: &AlgebraicTerm) -> bool {
        use crate::kernel::AlgebraicTermNode as T;
        crate::instrumentation::record_deterministic_work(1);
        if shared.ty() != &KernelType::Algebraic(native.algebraic_type.clone()) {
            return false;
        }
        match (shared.node(), &native.node) {
            (N::Variable(a), T::Variable(b)) => a == b,
            (N::AlgebraicCall(_), T::PureFunctionApplication { .. })
            | (N::AlgebraicRead(_), T::MemoryLoad { .. }) => {
                // Mixed call admission already compares imported arguments as
                // common roots, including their exact shared identities. Keep
                // that policy at this selected adapter, not native Eq/Ord.
                self.common_algebraic(
                    shared,
                    &crate::kernel::KernelTermImport::default().algebraic(native),
                )
            }
            // Constructors, matches and conditionals are not admitted here.
            // Refusal must not import all their fields, arms or branches.
            _ => false,
        }
    }

    fn common_algebraic(&mut self, a: &KernelTerm, b: &KernelTerm) -> bool {
        if a.ty() != b.ty() {
            return false;
        }
        if matches!(
            (a.node(), b.node()),
            (N::AlgebraicCall(_), N::AlgebraicCall(_))
        ) && !self.seen.insert((a.id(), b.id()))
        {
            return true;
        }
        match (a.node(), b.node()) {
            (N::Variable(a), N::Variable(b)) => a == b,
            (N::AlgebraicCall(a), N::AlgebraicCall(b)) => {
                a.name == b.name
                    && a.arguments.len() == b.arguments.len()
                    && a.arguments.iter().zip(&b.arguments).all(|(a, b)| {
                        self.call_argument(CallArgument::Shared(a), CallArgument::Shared(b))
                    })
            }
            (N::AlgebraicRead(a), N::AlgebraicRead(b)) => {
                let (am, ap) = a.parts();
                let (bm, bp) = b.parts();
                am.read_key() == bm.read_key() && self.shared_addresses(ap, bp)
            }
            _ => false,
        }
    }

    fn argument(&mut self, left: &A, right: &A) -> bool {
        match (left, right) {
            (A::SharedMachine(a), A::SharedMachine(b)) => {
                a.ty() == b.ty() && self.machine(a.operand_view(), b.operand_view())
            }
            (A::SharedMachine(a), A::Value(b)) | (A::Value(b), A::SharedMachine(a)) => {
                a.ty().program_type() == b.program_type()
                    && scalar(b).is_some_and(|b| self.machine(a.operand_view(), Operand::Old(b)))
            }
            (A::Value(a), A::Value(b)) => {
                if a.program_type() != b.program_type() {
                    return false;
                }
                match (scalar(a), scalar(b)) {
                    (Some(a), Some(b)) => self.machine(Operand::Old(a), Operand::Old(b)),
                    _ => match (a, b) {
                        (ProgramValue::Void, ProgramValue::Void) => true,
                        (ProgramValue::Pointer(a), ProgramValue::Pointer(b)) => {
                            self.pointer_value(a, b)
                        }
                        _ => false,
                    },
                }
            }
            (
                A::ArrayRef {
                    point: am,
                    pointer: ap,
                    element_type: at,
                },
                A::ArrayRef {
                    point: bm,
                    pointer: bp,
                    element_type: bt,
                },
            ) => {
                at == bt
                    && am.read_key() == bm.read_key()
                    && self.argument(&A::Value(ap.clone()), &A::Value(bp.clone()))
            }
            (A::Algebraic(a), A::Algebraic(b)) => self.algebraic(a, b),
            // Unsupported Integer payloads retain the existing alpha route;
            // written syntax is never collapsed to numeric observation keys.
            _ => false,
        }
    }
}

fn boolean_argument_word(root: &KernelTerm) -> Option<OldMachineTerm> {
    if let Some(value) = crate::kernel::BooleanOperandView::Shared(root).constant() {
        return Some(OldMachineTerm::bool_cast(
            MachineIntegerType::UInt8,
            OldConditionTerm::Constant(value),
        ));
    }
    if root.ty() == &KernelType::Program(ProgramType::Bool)
        && let N::Variable(variable) = root.node()
    {
        return Some(OldMachineTerm::Variable(*variable));
    }
    None
}

fn numeric_call(view: Operand<'_>) -> Option<(&str, Vec<CallArgument<'_>>)> {
    match view {
        Operand::Shared(root) => match root.node() {
            N::FloatCall(call) => Some((
                &call.name,
                call.arguments.iter().map(CallArgument::Shared).collect(),
            )),
            N::Call { name, arguments }
                if matches!(root.ty(), KernelType::Program(ty)
                    if MachineIntegerType::from_program_type(*ty).is_some()) =>
            {
                Some((name, arguments.iter().map(CallArgument::Shared).collect()))
            }
            _ => None,
        },
        Operand::Old(OldMachineTerm::ClickFunctionApplication { name, arguments }) => {
            Some((name, arguments.iter().map(CallArgument::Native).collect()))
        }
        _ => None,
    }
}

fn numeric_conversion(view: Operand<'_>) -> Option<((ProgramType, ProgramType), Operand<'_>)> {
    match view {
        Operand::Shared(root) => match root.node() {
            N::FloatConvert {
                source,
                destination,
                operand,
            } => Some(((*source, *destination), Operand::Shared(operand))),
            _ => None,
        },
        Operand::Old(OldMachineTerm::PureFunctionApplication { name, arguments }) => {
            let [operand] = arguments.as_slice() else {
                return None;
            };
            Some((
                crate::kernel::primitives::float_conversion::numeric_float_conversion_types(name)?,
                Operand::Old(operand),
            ))
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{KernelTermExport, VerificationSession};

    #[test]
    fn imported_scalar_call_arguments_compare_through_borrowed_carriers() {
        let _session = VerificationSession::enter();
        let word = |bits| {
            A::Value(ProgramValue::Bool(OldMachineTerm::Constant {
                format: MachineIntegerType::UInt8,
                bits,
            }))
        };
        let native = word(2);
        let imported = crate::kernel::KernelTermImport::default().argument(&native);
        let same = crate::kernel::KernelTermImport::default().argument(&native);
        let different = word(3);
        let retained = CallArgument::Shared(&imported);
        let compare = |a, b| Comparison::default().call_argument(a, b);
        assert!(compare(retained, CallArgument::Shared(&same)));
        assert!(compare(CallArgument::Native(&native), retained));
        assert!(!compare(retained, CallArgument::Native(&different)));
        assert!(!imported.has_cached_native_argument());
        assert!(!same.has_cached_native_argument());
    }

    #[test]
    fn shared_pointer_certification_preserves_complete_metadata_and_bounds_admission() {
        use crate::kernel::effective_type::{CAccessClass, CScalarClass};
        use crate::kernel::{
            IntegerTerm, ObjectTypeEvidence, OldAddress, OldPointer, SharedPointer, SubobjectBounds,
        };
        let _session = VerificationSession::enter();
        let base = OldPointer::new(
            OldAddress::symbolic(Variable(999980)),
            ProgramType::Int32Pointer,
        );
        let class = CAccessClass::Scalar(CScalarClass::Int);
        let bounds = SubobjectBounds {
            start: base.address().clone(),
            width: OldMachineTerm::constant(4),
        };
        let values = vec![
            base.clone(),
            base.clone().with_type(ProgramType::VoidPointer),
            base.clone()
                .with_provenance(std::sync::Arc::new(OldAddress::symbolic(Variable(999979)))),
            base.clone()
                .with_bounds_owner(Some(std::sync::Arc::new(OldAddress::symbolic(Variable(
                    999978,
                ))))),
            base.clone().with_bounds(Some(bounds)),
            base.clone().with_bounds(Some(SubobjectBounds {
                start: base.address().clone(),
                width: OldMachineTerm::IntegerToMachine {
                    destination: MachineIntegerType::Int32,
                    value: IntegerTerm::Variable(Variable(999977)).into(),
                },
            })),
            base.clone()
                .with_object_type_evidence(Some(ObjectTypeEvidence::parameter(
                    class.clone(),
                    3,
                    1,
                    false,
                ))),
            base.clone()
                .with_object_type_evidence(Some(ObjectTypeEvidence::parameter(class, 3, 2, false))),
            base.clone()
                .with_declared_object_class(Some(CAccessClass::Scalar(CScalarClass::Short))),
            base,
        ];
        for a in &values {
            for b in &values {
                let expected = Comparison::default().pointer_value(a, b);
                let (ar, br) = (
                    KernelTerm::shared_pointer_value(SharedPointer::import(a)),
                    KernelTerm::shared_pointer_value(SharedPointer::import(b)),
                );
                let (an, bn) = (
                    A::Value(ProgramValue::Pointer(a.clone())),
                    A::Value(ProgramValue::Pointer(b.clone())),
                );
                for (a, b) in [
                    (CallArgument::Shared(&ar), CallArgument::Shared(&br)),
                    (CallArgument::Shared(&ar), CallArgument::Native(&bn)),
                    (CallArgument::Native(&an), CallArgument::Shared(&br)),
                ] {
                    assert_eq!(Comparison::default().call_argument(a, b), expected);
                }
            }
        }
        // Shared bounds must not acquire the numeric identity shortcut.
        assert!(!Comparison::default().pointer_value(&values[5], &values[5]));
    }

    #[test]
    fn shared_captured_pointer_certification_preserves_memory_state() {
        use crate::kernel::{OldAddress, OldPointer, SharedPointer, SymbolicMemory};
        let _session = VerificationSession::enter();
        let memory = SymbolicMemory::new();
        let changed = memory.clone().store(
            OldAddress::null(),
            ProgramValue::Int32(OldMachineTerm::constant(1)),
        );
        let pointer = OldPointer::new(
            OldAddress::symbolic(Variable(999976)),
            ProgramType::Int32Pointer,
        );
        let root = KernelTerm::shared_pointer_value(SharedPointer::import(&pointer));
        let shared = |memory: &SymbolicMemory| {
            KernelTerm::shared_array_reference(
                crate::kernel::ProgramPoint::at(&crate::kernel::intern_memory_ref(memory)),
                root.clone(),
                ProgramType::Int32,
            )
        };
        let a = shared(&memory);
        for (memory, expected) in [(&memory, true), (&changed, false)] {
            let b = shared(memory);
            let native = A::ArrayRef {
                point: crate::kernel::ProgramPoint::of_memory(memory),
                pointer: ProgramValue::Pointer(pointer.clone()),
                element_type: ProgramType::Int32,
            };
            assert_eq!(
                Comparison::default()
                    .call_argument(CallArgument::Shared(&a), CallArgument::Shared(&b)),
                expected
            );
            assert_eq!(
                Comparison::default()
                    .call_argument(CallArgument::Shared(&a), CallArgument::Native(&native)),
                expected
            );
        }
    }

    #[test]
    fn shared_algebraic_read_certification_preserves_address_and_state_identity() {
        use crate::kernel::{
            AlgebraicTermNode, AlgebraicType, OldAddress, SharedAddress, SymbolicMemory,
        };
        let _session = VerificationSession::enter();
        let memory = crate::kernel::intern_memory_ref(&SymbolicMemory::new());
        let changed = crate::kernel::intern_memory_ref(&memory.memory().clone().store(
            OldAddress::null(),
            ProgramValue::Int32(OldMachineTerm::constant(1)),
        ));
        let pointer = OldAddress::symbolic(Variable(999974));
        let other = OldAddress::symbolic(Variable(999973));
        let ty = AlgebraicType::parameter("T".into());
        let root = KernelTerm::algebraic_read(
            ty.clone(),
            crate::kernel::ProgramPoint::at(&memory),
            SharedAddress::import(&pointer),
        );
        for (state, address, expected) in [
            (&memory, &pointer, true),
            (&changed, &pointer, false),
            (&memory, &other, false),
        ] {
            let right = KernelTerm::algebraic_read(
                ty.clone(),
                crate::kernel::ProgramPoint::at(state),
                SharedAddress::import(address),
            );
            let native = AlgebraicTerm {
                algebraic_type: ty.clone(),
                node: AlgebraicTermNode::MemoryLoad {
                    point: crate::kernel::ProgramPoint::at(&state.clone()),
                    pointer: Box::new(address.clone()),
                },
            };
            assert_eq!(
                Comparison::default().common_algebraic(&root, &right),
                expected
            );
            assert_eq!(
                Comparison::default().mixed_algebraic(&root, &native),
                expected
            );
        }
    }

    #[test]
    fn shared_pointer_opaque_indices_keep_the_native_refusal() {
        use crate::kernel::{
            IntegerTerm, KernelAddressOffset, OldAddress, OldPointer, SharedAddress, SharedPointer,
        };
        let _session = VerificationSession::enter();
        let native = OldMachineTerm::PureFunctionApplication {
            name: "opaque_index".into(),
            arguments: vec![OldMachineTerm::IntegerToMachine {
                destination: MachineIntegerType::Int32,
                value: IntegerTerm::Variable(Variable(999975)).into(),
            }],
        };
        let index = KernelTerm::retained_native_machine_operand(MachineIntegerType::Int32, &native);
        assert!(matches!(index.node(), N::WrittenMachine(_)));
        let base = SharedPointer::import(&OldPointer::new(
            OldAddress::null(),
            ProgramType::Int32Pointer,
        ));
        let mut value = base.node().clone();
        value.address = SharedAddress::new(
            value.address.node().base.clone(),
            KernelAddressOffset::Int32Scaled {
                value: index,
                byte_width: 4,
            }
            .into_shared()
            .unwrap(),
        );
        value.provenance = value.address.clone();
        let root = KernelTerm::shared_pointer_value(SharedPointer::new(value));
        assert!(
            !Comparison::default()
                .call_argument(CallArgument::Shared(&root), CallArgument::Shared(&root))
        );
    }

    #[test]
    fn boolean_argument_certification_keeps_literal_raw_word_and_logical_admission() {
        let _session = VerificationSession::enter();
        let mut cases = Vec::new();
        for condition in [
            OldConditionTerm::Constant(false),
            OldConditionTerm::Constant(true),
            OldConditionTerm::Variable(Variable(999983)),
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left: Box::new(OldMachineTerm::Variable(Variable(999983))),
                right: Box::new(OldMachineTerm::constant(4)),
            },
            OldConditionTerm::BoolIf {
                condition: Box::new(OldConditionTerm::Variable(Variable(999983))),
                then_condition: Box::new(OldConditionTerm::Constant(true)),
                else_condition: Box::new(OldConditionTerm::Constant(false)),
            },
        ] {
            let root = crate::kernel::KernelTermImport::default().condition(&condition);
            let native = A::Value(ProgramValue::Bool(OldMachineTerm::bool_cast(
                MachineIntegerType::UInt8,
                condition,
            )));
            cases.push((root, native));
        }
        cases.push((
            KernelTerm::variable(KernelType::Program(ProgramType::Bool), Variable(999983)),
            A::Value(ProgramValue::Bool(OldMachineTerm::Variable(Variable(
                999983,
            )))),
        ));
        let raw = A::Value(ProgramValue::Bool(OldMachineTerm::Constant {
            format: MachineIntegerType::UInt8,
            bits: 2,
        }));
        cases.push((
            crate::kernel::KernelTermImport::default().argument(&raw),
            raw,
        ));
        for (root, native) in cases {
            let expected = Comparison::default().argument(&native, &native);
            let exports = KernelTermExport::machine_export_count();
            for (left, right) in [
                (CallArgument::Shared(&root), CallArgument::Native(&native)),
                (CallArgument::Native(&native), CallArgument::Shared(&root)),
                (CallArgument::Shared(&root), CallArgument::Shared(&root)),
            ] {
                assert_eq!(Comparison::default().call_argument(left, right), expected);
            }
            assert_eq!(KernelTermExport::machine_export_count(), exports);
        }
    }

    #[test]
    fn mixed_algebraic_call_certification_preserves_imported_argument_identity() {
        use crate::kernel::{AlgebraicTermNode, AlgebraicType, IntegerTerm};
        let _session = VerificationSession::enter();
        let native = AlgebraicTerm {
            algebraic_type: AlgebraicType::parameter("T".into()),
            node: AlgebraicTermNode::PureFunctionApplication {
                name: "identity_boundary".into(),
                arguments: vec![A::Value(ProgramValue::Int32(
                    OldMachineTerm::IntegerToMachine {
                        destination: MachineIntegerType::Int32,
                        value: IntegerTerm::Variable(Variable(999982)).into(),
                    },
                ))],
            },
        };
        let shared = crate::kernel::KernelTermImport::default().algebraic(&native);
        // The existing mixed route uses common argument identity; the native
        // syntax route still refuses this conversion. Consolidation keeps both.
        assert!(!algebraic_equal(&native, &native));
        assert!(Comparison::default().mixed_algebraic(&shared, &native));
    }

    #[test]
    fn retained_numeric_calls_keep_native_admission_without_argument_exports() {
        let _session = VerificationSession::enter();
        let variable = OldMachineTerm::Variable(Variable(999984));
        for argument in [
            A::Value(ProgramValue::Float32(variable.clone())),
            A::Value(ProgramValue::Float64(variable.clone())),
            A::Value(ProgramValue::Float32(OldMachineTerm::Float32Negate(
                Box::new(variable),
            ))),
        ] {
            let native = OldMachineTerm::ClickFunctionApplication {
                name: "numeric_boundary".into(),
                arguments: vec![argument],
            };
            let root = crate::kernel::KernelTermImport::default()
                .machine(MachineIntegerType::Int32, &native);
            assert!(matches!(root.node(), N::Call { .. }));
            let expected =
                Comparison::default().machine(Operand::Old(&native), Operand::Old(&native));
            let exports = KernelTermExport::float_export_count();
            for (left, right) in [
                (Operand::Shared(&root), Operand::Old(&native)),
                (Operand::Old(&native), Operand::Shared(&root)),
            ] {
                assert_eq!(Comparison::default().machine(left, right), expected);
            }
            assert_eq!(KernelTermExport::float_export_count(), exports);
        }
    }

    #[test]
    fn retained_float_conversions_keep_native_certification_admission() {
        let _session = VerificationSession::enter();
        let variable = OldMachineTerm::Variable(Variable(999985));
        for source in [
            variable.clone(),
            OldMachineTerm::opaque_conversion("c_float64_to_float32", variable.clone()),
            OldMachineTerm::Float32Negate(Box::new(variable)),
        ] {
            let native = OldMachineTerm::opaque_conversion("c_float32_to_int32", source);
            let root = crate::kernel::KernelTermImport::default()
                .machine(MachineIntegerType::Int32, &native);
            let expected =
                Comparison::default().machine(Operand::Old(&native), Operand::Old(&native));
            let exports = KernelTermExport::machine_export_count();
            assert_eq!(
                Comparison::default().machine(Operand::Shared(&root), Operand::Old(&native)),
                expected
            );
            assert_eq!(
                Comparison::default().machine(Operand::Old(&native), Operand::Shared(&root)),
                expected
            );
            assert_eq!(KernelTermExport::machine_export_count(), exports);
        }
    }

    fn retained_leaf(value: u32) -> KernelTerm {
        KernelTerm::retained_native_machine_operand(
            MachineIntegerType::UInt64,
            &OldMachineTerm::ClickFunctionApplication {
                name: "strict_leaf".into(),
                arguments: vec![A::Value(ProgramValue::Int32(OldMachineTerm::constant(
                    value,
                )))],
            },
        )
    }
    fn condition(argument: KernelTerm) -> OldConditionTerm {
        OldConditionTerm::Compare {
            format: MachineIntegerType::UInt8,
            relation: CompareRelation::LessEqual,
            left: Box::new(OldMachineTerm::Constant {
                format: MachineIntegerType::UInt8,
                bits: 48,
            }),
            right: Box::new(OldMachineTerm::ClickFunctionApplication {
                name: "strict_digit".into(),
                arguments: vec![A::SharedMachine(
                    SharedMachineIntegerTerm::from_shared(MachineIntegerType::UInt64, argument)
                        .unwrap(),
                )],
            }),
        }
    }
    fn algebraic_call(argument: AlgebraicTerm, name: &str) -> AlgebraicTerm {
        let application = crate::kernel::SharedPureApplication::intern(
            "retained_length".into(),
            vec![A::Algebraic(argument.clone())],
        );
        let root = crate::kernel::KernelTermImport::default()
            .machine_call(MachineIntegerType::UInt64, &application);
        AlgebraicTerm {
            algebraic_type: argument.algebraic_type.clone(),
            node: crate::kernel::AlgebraicTermNode::PureFunctionApplication {
                name: name.into(),
                arguments: vec![
                    A::Algebraic(argument),
                    A::SharedMachine(
                        SharedMachineIntegerTerm::from_shared(MachineIntegerType::UInt64, root)
                            .unwrap(),
                    ),
                ],
            },
        }
    }

    #[test]
    fn algebraic_call_certification_ignores_allocation_but_keeps_written_inputs() {
        use crate::kernel::{
            AlgebraicTermNode, AlgebraicType, OldAddress, SymbolicMemory, Variable,
        };
        let _session = VerificationSession::enter();
        let ty = AlgebraicType::parameter("T".into());
        let variable = AlgebraicTerm {
            algebraic_type: ty.clone(),
            node: AlgebraicTermNode::Variable(Variable(995950)),
        };
        let left = algebraic_call(variable.clone(), "wrap");
        let right = algebraic_call(variable.clone(), "wrap");
        // Structural argument imports now reuse the same call root; no fresh
        // generic argument wrapper separates these identical producers.
        assert_eq!(left, right);
        let claim = |value: AlgebraicTerm| {
            Proposition::Equal(
                Term::Algebraic(value.into()),
                Term::Algebraic(variable.clone().into()),
            )
        };
        let exports = KernelTermExport::machine_export_count();
        assert!(algebraic_equal(&left, &right));
        assert!(propositions_alpha_equivalent(
            &claim(left.clone()),
            &claim(right)
        ));
        assert!(!algebraic_equal(
            &left,
            &algebraic_call(variable.clone(), "other")
        ));
        let changed = AlgebraicTerm {
            algebraic_type: ty.clone(),
            node: AlgebraicTermNode::Variable(Variable(995951)),
        };
        assert!(!algebraic_equal(&left, &algebraic_call(changed, "wrap")));
        let memory = SymbolicMemory::new();
        let other = memory
            .clone()
            .store(OldAddress::null(), ProgramValue::Int32(1u32.into()));
        let read = |memory: &SymbolicMemory| AlgebraicTerm {
            algebraic_type: ty.clone(),
            node: AlgebraicTermNode::MemoryLoad {
                point: crate::kernel::ProgramPoint::at(&crate::kernel::intern_memory_ref(memory)),
                pointer: Box::new(OldAddress::null()),
            },
        };
        assert!(!algebraic_equal(
            &algebraic_call(read(&memory), "wrap"),
            &algebraic_call(read(&other), "wrap")
        ));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }

    #[test]
    fn fresh_retained_payloads_have_one_written_certification_syntax() {
        let _session = VerificationSession::enter();
        let left = condition(retained_leaf(7));
        let right = condition(retained_leaf(7));
        assert_ne!(left, right, "exercise distinct producer IDs");
        let exports = KernelTermExport::machine_export_count();
        assert!(conditions_equal(&left, &right));
        let left = Proposition::condition_is(left, true);
        let right = Proposition::condition_is(right, true);
        assert!(propositions_alpha_equivalent(&left, &right));
        let lines = crate::kernel::fact_stability::capture(|| {
            crate::kernel::fact_stability::compare(
                "retained syntax",
                &left,
                &crate::kernel::fact_stability::FactFree::Term(right),
            );
        });
        assert!(lines.is_empty(), "{lines:?}");
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }
    #[test]
    fn retained_syntax_rejects_changed_payload_operator_and_written_format() {
        let _session = VerificationSession::enter();
        assert!(!conditions_equal(
            &condition(retained_leaf(7)),
            &condition(retained_leaf(8))
        ));
        let binary = |operator| {
            KernelTerm::machine_binary_shared(
                MachineIntegerType::UInt64,
                operator,
                [retained_leaf(7), retained_leaf(9)],
            )
        };
        assert!(!conditions_equal(
            &condition(binary(MachineBinaryOp::Add)),
            &condition(binary(MachineBinaryOp::Subtract))
        ));
        let left = condition(retained_leaf(7));
        let mut right = left.clone();
        if let OldConditionTerm::Compare { format, .. } = &mut right {
            *format = MachineIntegerType::Int8;
        }
        assert!(!conditions_equal(&left, &right));
        let mut right = left.clone();
        if let OldConditionTerm::Compare { relation, .. } = &mut right {
            *relation = CompareRelation::LessThan;
        }
        assert!(!conditions_equal(&left, &right));
    }
    #[test]
    fn retained_syntax_keeps_states_and_pointer_qualifiers_exact() {
        let _session = VerificationSession::enter();
        let memory = crate::kernel::SymbolicMemory::new();
        let changed = memory.clone().store(
            crate::kernel::OldAddress::null(),
            ProgramValue::Int32(OldMachineTerm::constant(1)),
        );
        let read = |memory: &crate::kernel::SymbolicMemory| {
            OldMachineTerm::read_named(
                ProgramPoint::at(&(crate::kernel::intern_memory_ref(memory))),
                Box::new(crate::kernel::OldAddress::null()),
                crate::kernel::LoadKind::Int32,
            )
        };
        assert!(
            !Comparison::default()
                .machine(Operand::Old(&read(&memory)), Operand::Old(&read(&changed)))
        );
        let pointer = crate::kernel::OldPointer::new(
            crate::kernel::OldAddress::null(),
            crate::kernel::ProgramType::Int32Pointer,
        );
        let qualified = pointer.clone().with_declared_object_class(Some(
            crate::kernel::effective_type::CAccessClass::Scalar(
                crate::kernel::effective_type::CScalarClass::Int,
            ),
        ));
        assert!(!Comparison::default().argument(
            &A::Value(ProgramValue::Pointer(pointer)),
            &A::Value(ProgramValue::Pointer(qualified))
        ));
    }
    #[test]
    fn retained_syntax_preserves_argument_order_and_cast_spelling() {
        let _session = VerificationSession::enter();
        let call = |a, b| OldMachineTerm::ClickFunctionApplication {
            name: "ordered_call".into(),
            arguments: vec![a, b],
        };
        let argument = |value| {
            A::SharedMachine(
                SharedMachineIntegerTerm::from_shared(
                    MachineIntegerType::UInt64,
                    retained_leaf(value),
                )
                .unwrap(),
            )
        };
        let left = call(argument(7), argument(9));
        let right = call(argument(9), argument(7));
        assert!(!Comparison::default().machine(Operand::Old(&left), Operand::Old(&right)));
        let cast = |encoding, source, destination| {
            KernelTerm::machine_cast_shared(
                encoding,
                source,
                destination,
                KernelTerm::retained_native_machine_operand(
                    source,
                    &OldMachineTerm::Variable(crate::kernel::Variable(711)),
                ),
            )
        };
        let generic = cast(
            MachineCastSpelling::Generic,
            MachineIntegerType::UInt32,
            MachineIntegerType::UInt64,
        );
        let legacy = cast(
            MachineCastSpelling::UInt64From32,
            MachineIntegerType::UInt32,
            MachineIntegerType::UInt64,
        );
        let source = cast(
            MachineCastSpelling::Generic,
            MachineIntegerType::Int32,
            MachineIntegerType::UInt64,
        );
        let destination = cast(
            MachineCastSpelling::Generic,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
        );
        for different in [&legacy, &source, &destination] {
            assert!(
                !Comparison::default()
                    .machine(Operand::Shared(&generic), Operand::Shared(different))
            );
        }
        assert!(
            Comparison::default().machine(Operand::Shared(&generic), Operand::Shared(&generic))
        );
    }

    #[test]
    fn retained_syntax_preserves_captured_and_pointer_index_states() {
        use crate::kernel::{
            AddressOffset, LoadKind, OldAddress, OldPointer, ProgramType, SymbolicMemory, Variable,
        };
        let _session = VerificationSession::enter();
        let memory = SymbolicMemory::new();
        let other = memory.clone().store(
            OldAddress::null(),
            ProgramValue::Int32(OldMachineTerm::constant(5)),
        );
        let pointer = |retained_state: &SymbolicMemory| {
            OldPointer::new(
                OldAddress {
                    base: "indexed".into(),
                    offset: OldAddressOffset::Int32Scaled {
                        value: SharedMachineIntegerTerm::index(
                            MachineIntegerType::Int32,
                            OldMachineTerm::read_named(
                                ProgramPoint::at(
                                    &(crate::kernel::intern_memory_ref(retained_state)),
                                ),
                                Box::new(OldAddress::symbolic(Variable(712))),
                                LoadKind::Int32,
                            ),
                        ),
                        byte_width: 4,
                    }
                    .into(),
                },
                ProgramType::Int32Pointer,
            )
        };
        let captured = |retained_state: &SymbolicMemory, address| A::ArrayRef {
            point: ProgramPoint::of_memory(retained_state),
            pointer: ProgramValue::Pointer(address),
            element_type: ProgramType::Int32,
        };
        let left = captured(&memory, pointer(&memory));
        assert!(Comparison::default().argument(&left, &captured(&memory, pointer(&memory))));
        assert!(!Comparison::default().argument(&left, &captured(&other, pointer(&memory))));
        assert!(!Comparison::default().argument(&left, &captured(&memory, pointer(&other))));
    }

    #[test]
    fn retained_syntax_preserves_unchecked_evidence_and_hidden_declaration_class() {
        use crate::kernel::effective_type::{CAccessClass, CScalarClass};
        use crate::kernel::{ObjectTypeEvidence, OldAddress, OldPointer, ProgramType};
        let _session = VerificationSession::enter();
        let base = OldPointer::new(OldAddress::null(), ProgramType::Int32Pointer);
        let class = CAccessClass::Scalar(CScalarClass::Int);
        let evidence = |fingerprint| ObjectTypeEvidence {
            class: class.clone(),
            checked: false,
            premise_fingerprint: fingerprint,
            premises: Default::default(),
        };
        let a = base.clone().with_object_type_evidence(Some(evidence(1)));
        let b = base.clone().with_object_type_evidence(Some(evidence(2)));
        assert_eq!(a.object_type_evidence(), b.object_type_evidence());
        assert_eq!(a.object_class(), b.object_class());
        assert!(!Comparison::default().pointer_value(&a, &b));
        let checked = ObjectTypeEvidence::from(class);
        let a = base
            .clone()
            .with_declared_object_class(Some(CAccessClass::Scalar(CScalarClass::Short)))
            .with_object_type_evidence(Some(checked.clone()));
        let b = base
            .with_declared_object_class(Some(CAccessClass::Scalar(CScalarClass::Long)))
            .with_object_type_evidence(Some(checked));
        assert_eq!(a.object_origin_evidence(), b.object_origin_evidence());
        assert_eq!(a.object_class(), b.object_class());
        assert!(!Comparison::default().pointer_value(&a, &b));
        assert!(Comparison::default().pointer_value(&a, &a.clone()));
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../../scaling_tests/kernel/api/contract_certification/retained_syntax.rs");
    }
}

#[cfg(test)]
mod float_call_tests {
    use super::*;
    #[test]
    fn float_calls_keep_native_certification_admission_without_exports() {
        let _session = crate::kernel::VerificationSession::enter();
        for argument in [
            A::Value(ProgramValue::Bool(OldMachineTerm::Variable(Variable(
                1008213,
            )))),
            A::Value(ProgramValue::Bool(OldMachineTerm::Constant {
                format: MachineIntegerType::UInt8,
                bits: 1,
            })),
            A::Value(ProgramValue::Bool(OldMachineTerm::uint32_constant(1))),
            A::Value(ProgramValue::Float32(OldMachineTerm::Variable(Variable(
                1008210,
            )))),
            A::Integer(crate::kernel::IntegerTerm::Variable(Variable(1008211)).into()),
            A::Value(ProgramValue::Float32(OldMachineTerm::Float32Negate(
                Box::new(OldMachineTerm::Variable(Variable(1008212))),
            ))),
        ] {
            let native = OldMachineTerm::opaque_conversion(
                "c_float32_to_int32",
                OldMachineTerm::ClickFunctionApplication {
                    name: "float_certification".into(),
                    arguments: vec![argument],
                },
            );
            let root = crate::kernel::KernelTermImport::default()
                .machine(MachineIntegerType::Int32, &native);
            let expected =
                Comparison::default().machine(Operand::Old(&native), Operand::Old(&native));
            let exports = crate::kernel::KernelTermExport::float_export_count();
            assert_eq!(
                Comparison::default().machine(Operand::Shared(&root), Operand::Old(&native)),
                expected
            );
            assert_eq!(
                Comparison::default().machine(Operand::Old(&native), Operand::Shared(&root)),
                expected
            );
            assert_eq!(
                crate::kernel::KernelTermExport::float_export_count(),
                exports
            );
        }
    }
}
