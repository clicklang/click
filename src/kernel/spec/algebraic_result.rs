//! Both evaluator origins retain common expression roots. The origin tag keeps
//! the existing checking/producer handoffs and equality classes distinct.
use super::*;

#[derive(Clone, Debug)]
pub(super) enum AlgebraicResult {
    Imported(KernelTerm),
    Shared(KernelTerm),
}
impl From<AlgebraicTerm> for AlgebraicResult {
    fn from(value: AlgebraicTerm) -> Self {
        Self::Imported(KernelTermImport::default().algebraic(&value))
    }
}
impl AlgebraicResult {
    pub(super) fn root(&self) -> &KernelTerm {
        match self {
            Self::Imported(root) | Self::Shared(root) => root,
        }
    }
    pub(super) fn algebraic_type(&self) -> &AlgebraicType {
        let KernelType::Algebraic(ty) = self.root().ty() else {
            unreachable!("algebraic result type")
        };
        ty
    }
    pub(super) fn is_constructor(&self) -> bool {
        matches!(self.root().node(), KernelTermNode::Constructor(_))
            || (matches!(self, Self::Imported(_))
                && matches!(self.root().node(), KernelTermNode::Legacy(_))
                && self.native_constructor().is_some())
    }
    pub(super) fn retain_native(value: AlgebraicTerm, retain: bool) -> Self {
        let root = KernelTermImport::default().algebraic(&value);
        if retain {
            Self::Shared(root)
        } else {
            Self::Imported(root)
        }
    }
    pub(super) fn native_constructor(&self) -> Option<&AlgebraicTerm> {
        let root = self.root();
        if !matches!(root.node(), KernelTermNode::Constructor(_))
            && !(matches!(self, Self::Imported(_))
                && matches!(root.node(), KernelTermNode::Legacy(_)))
        {
            return None;
        }
        let ProgramValue::Parameter(value) = root.algebraic_native_value()? else {
            unreachable!("algebraic constructor reading")
        };
        matches!(value.node, AlgebraicTermNode::Constructor { .. }).then_some(value)
    }
    pub(super) fn into_kernel(self) -> KernelTerm {
        match self {
            Self::Imported(root) | Self::Shared(root) => root,
        }
    }
    pub(super) fn into_native_compat(self) -> AlgebraicTerm {
        KernelTermExport::default()
            .algebraic(&self.into_kernel())
            .expect("algebraic result compatibility boundary")
    }
}
impl PartialEq for AlgebraicResult {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Shared(a), Self::Shared(b)) => a == b,
            (Self::Imported(a), Self::Imported(b)) => {
                a == b || self.clone().into_native_compat() == other.clone().into_native_compat()
            }
            _ => false,
        }
    }
}
impl Eq for AlgebraicResult {}

/// Program-carried parameters retain their program envelope; logical fields
/// retain a bare root. Imported and retained origins keep their existing scope
/// and equality contracts, without storing a native field payload.
#[derive(Clone, Debug)]
pub(super) enum AlgebraicFieldResult {
    Imported(KernelTerm),
    Shared(KernelTerm),
}
impl AlgebraicFieldResult {
    pub(super) fn root(&self) -> &KernelTerm {
        match self {
            Self::Imported(root) | Self::Shared(root) => root,
        }
    }
    pub(super) fn from_native(value: AlgebraicValue) -> Self {
        Self::Imported(KernelTermImport::default().match_field(&value))
    }
    pub(super) fn from_program(value: SpecValue) -> Self {
        match value {
            SpecValue::Native(value) => Self::from_native(AlgebraicValue::Program(value)),
            value => {
                let root = value.common_operand();
                Self::Shared(if matches!(root.ty(), KernelType::Algebraic(_)) {
                    KernelTerm::program_parameter(root)
                } else {
                    root
                })
            }
        }
    }
    pub(super) fn from_algebraic(value: AlgebraicResult) -> Self {
        match value {
            AlgebraicResult::Imported(root) => Self::Imported(root),
            AlgebraicResult::Shared(root) => Self::Shared(root),
        }
    }
    pub(super) fn has_type(&self, expected: &AlgebraicValueType) -> bool {
        match self.root().ty() {
            KernelType::Algebraic(ty) => ty.value_type() == *expected,
            KernelType::Integer => *expected == AlgebraicValueType::Integer,
            KernelType::Bool => *expected == AlgebraicValueType::Program(ProgramType::Bool),
            KernelType::Program(ty) => match expected {
                AlgebraicValueType::Program(expected) => ty == expected,
                AlgebraicValueType::ObjectPointer(_, _) => SpecValue::Shared(self.root().clone())
                    .native_payload()
                    .is_some_and(|value| expected.accepts_program_value(value)),
                _ => false,
            },
            _ => false,
        }
    }
    pub(super) fn program_compat(&self) -> Option<ProgramValue> {
        matches!(self.root().ty(), KernelType::Program(ty) if ty.is_pointer())
            .then(|| SpecValue::Shared(self.root().clone()).into_native())
    }
    pub(super) fn with_checked_program(self, value: ProgramValue) -> Self {
        let value = SpecValue::Shared(self.into_kernel()).retain_checked_pointer(value);
        Self::Imported(value.common_operand())
    }
    pub(super) fn without_pointer_constant(self) -> Self {
        let root = self.root();
        if !matches!(root.ty(), KernelType::Program(ty) if ty.is_pointer()) {
            return self;
        }
        if let Some(pointer) = root.pointer_payload() {
            let payload = pointer.node();
            let volatile = payload.qualifiers.as_ref().is_some_and(|q| q.volatile);
            let result = root.with_pointer_payload(pointer.with_binding_type_and_qualifiers(
                payload.program_type,
                volatile,
                false,
            ));
            match self {
                Self::Imported(_) => Self::Imported(result),
                Self::Shared(_) => Self::Shared(result),
            }
        } else {
            Self::from_native(AlgebraicValue::Program(
                SpecValue::Shared(self.into_kernel())
                    .into_native()
                    .with_pointer_pointee_constant(false),
            ))
        }
    }
    pub(super) fn into_kernel(self) -> KernelTerm {
        match self {
            Self::Imported(root) | Self::Shared(root) => root,
        }
    }
    pub(super) fn into_native(self) -> AlgebraicValue {
        match KernelTermExport::default()
            .argument(&self.into_kernel())
            .expect("selected field output")
        {
            PureFunctionArgument::Value(value) => AlgebraicValue::Program(value),
            PureFunctionArgument::Integer(value) => AlgebraicValue::Integer(value.as_ref().clone()),
            PureFunctionArgument::Algebraic(value) => AlgebraicValue::Algebraic(value),
            _ => unreachable!("constructor field"),
        }
    }
    pub(super) fn integer(&self) -> Option<IntegerResult> {
        (self.root().ty() == &KernelType::Integer)
            .then(|| IntegerResult::from_kernel(self.root().clone()))
    }
}
impl PartialEq for AlgebraicFieldResult {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Shared(a), Self::Shared(b)) => a == b,
            (Self::Imported(a), Self::Imported(b)) => {
                a == b || self.clone().into_native() == other.clone().into_native()
            }
            _ => false,
        }
    }
}
impl Eq for AlgebraicFieldResult {}

#[cfg(test)]
mod storage_tests {
    use super::*;
    use crate::kernel::VerificationSession;

    #[test]
    fn common_algebraic_storage_keeps_imported_and_retained_equality_classes() {
        let _session = VerificationSession::enter();
        let ProgramValue::Pointer(pointer) =
            crate::kernel::symbolic_call_result(ProgramType::Int32Pointer, Variable(1012100))
        else {
            unreachable!("typed pointer")
        };
        let field = |constant| {
            AlgebraicValue::Program(ProgramValue::Pointer(
                pointer.clone().with_pointee_constant(constant),
            ))
        };
        let left_field = AlgebraicFieldResult::from_native(field(false));
        let right_field = AlgebraicFieldResult::from_native(field(true));
        assert_eq!(
            left_field, right_field,
            "imported fields keep native equality"
        );
        let left_root = left_field.clone().into_kernel();
        let right_root = right_field.clone().into_kernel();
        assert_ne!(left_field, AlgebraicFieldResult::Shared(left_root.clone()));
        assert_ne!(
            AlgebraicFieldResult::Shared(left_root),
            AlgebraicFieldResult::Shared(right_root)
        );
        let ty = KernelMatch::test_scrutinee(vec![AlgebraicValueType::Program(
            ProgramType::Int32Pointer,
        )])
        .algebraic_type;
        let constructor = |constant| AlgebraicTerm {
            algebraic_type: ty.clone(),
            node: AlgebraicTermNode::Constructor {
                variant: "Arm".into(),
                fields: vec![field(constant)],
            },
        };
        let left = AlgebraicResult::from(constructor(false));
        let right = AlgebraicResult::from(constructor(true));
        assert_eq!(left, right, "imported results keep native equality");
        assert_ne!(left, AlgebraicResult::Shared(left.clone().into_kernel()));
        assert_ne!(
            AlgebraicResult::Shared(left.into_kernel()),
            AlgebraicResult::Shared(right.into_kernel())
        );
    }

    #[test]
    fn algebraic_result_and_field_storage_release_native_integer_children() {
        let _session = VerificationSession::enter();
        let ty = KernelMatch::test_scrutinee(vec![AlgebraicValueType::Integer]).algebraic_type;
        for as_field in [false, true] {
            let child: SharedIntegerTerm = IntegerTerm::Add(
                IntegerTerm::var(Variable(1012110)).into(),
                IntegerTerm::constant_i64(7).into(),
            )
            .into();
            let weak = child.downgrade();
            let source = AlgebraicTerm {
                algebraic_type: ty.clone(),
                node: AlgebraicTermNode::Constructor {
                    variant: "Arm".into(),
                    fields: vec![AlgebraicValue::Integer(IntegerTerm::Multiply(
                        child.clone(),
                        child,
                    ))],
                },
            };
            let root = if as_field {
                AlgebraicFieldResult::from_native(AlgebraicValue::Algebraic(source)).into_kernel()
            } else {
                AlgebraicResult::from(source).into_kernel()
            };
            assert!(weak.upgrade().is_none(), "as_field={as_field}");
            let KernelTermNode::Constructor(constructor) = root.node() else {
                panic!("common constructor")
            };
            assert_eq!(constructor.fields.len(), 1);
            assert!(!root.has_cached_native_argument());
        }
    }

    #[test]
    fn imported_fields_preserve_raw_boolean_words_and_program_parameter_envelopes() {
        let _session = VerificationSession::enter();
        let raw_bool = AlgebraicValue::Program(ProgramValue::Bool(MachineTerm::constant(2)));
        assert_eq!(
            AlgebraicFieldResult::from_native(raw_bool.clone()).into_native(),
            raw_bool
        );
        let value = KernelMatch::test_scrutinee(vec![]);
        let program = AlgebraicValue::Program(ProgramValue::Parameter(Box::new(value.clone())));
        let logical = AlgebraicValue::Algebraic(value);
        let program_field = AlgebraicFieldResult::from_native(program.clone());
        let logical_field = AlgebraicFieldResult::from_native(logical.clone());
        assert_ne!(program_field.root().ty(), logical_field.root().ty());
        assert_eq!(program_field.into_native(), program);
        assert_eq!(logical_field.into_native(), logical);
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/spec/algebraic_result.rs");
}
