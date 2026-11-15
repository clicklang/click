//! Logical Bool operands of machine conversions. Import/export preserves the
//! written comparison format, even when fact equality identifies formats.
use super::*;
mod comparison;
mod pointer_comparison;

/// Borrow a Boolean root or an exact native compatibility payload. Inspecting
/// this view never exports children, consults facts, or selects a branch.
#[derive(Clone, Copy)]
pub(crate) enum BooleanOperandView<'a> {
    Shared(&'a KernelTerm),
    Native(&'a ConditionTerm),
}

impl<'a> BooleanOperandView<'a> {
    /// Visit dependency-bearing Boolean leaves, sharing a common connective
    /// once. Call arguments and native opaque leaves keep the reader's rules.
    pub(crate) fn for_each_dependency_leaf(self, mut visit: impl FnMut(Self)) {
        let mut pending = vec![self];
        let mut seen = std::collections::HashSet::new();
        while let Some(view) = pending.pop() {
            if let Self::Shared(root) = view
                && !seen.insert(root.id())
            {
                continue;
            }
            crate::instrumentation::record_deterministic_work(1);
            if let Some(children) = view.conditional() {
                pending.extend(children.into_iter().rev());
            } else if let Some(children) = view.equality() {
                pending.extend(children.into_iter().rev());
            } else {
                visit(view);
            }
        }
    }

    /// Exact native Boolean identity, without exporting connective trees or
    /// primitive comparison operands. Load authority is never consulted here.
    pub(crate) fn syntax_equal(self, other: Self) -> bool {
        self.syntax_equal_by(other, |a, b| {
            crate::kernel::machine_operand_syntax_cmp(a, b).is_eq()
        })
    }

    /// The callback supplies exact native machine syntax equality. Callers
    /// outside the machine correspondence traversal may reuse its syntax memo;
    /// callers inside it use the non-reentrant reader above.
    pub(crate) fn syntax_equal_by(
        self,
        other: Self,
        mut machine_equal: impl FnMut(MachineOperandView<'a>, MachineOperandView<'a>) -> bool,
    ) -> bool {
        use crate::kernel::machine_integer::comparison::{FactOperand, fact_operand_identity};
        let mut pending = vec![(self, other)];
        let mut seen = std::collections::HashSet::new();
        while let Some((left, right)) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            if let (Self::Shared(a), Self::Shared(b)) = (left, right) {
                if a == b || !seen.insert((a.id(), b.id())) {
                    continue;
                }
            }
            if let (Some(a), Some(b)) = (left.native_leaf(), right.native_leaf()) {
                if a != b {
                    return false;
                }
                continue;
            }
            match (left.conditional(), right.conditional()) {
                (Some(a), Some(b)) => {
                    pending.extend(a.into_iter().zip(b));
                    continue;
                }
                (None, None) => {}
                _ => return false,
            }
            match (left.equality(), right.equality()) {
                (Some(a), Some(b)) => {
                    pending.extend(a.into_iter().zip(b));
                    continue;
                }
                (None, None) => {}
                _ => return false,
            }
            match (left.comparison(), right.comparison()) {
                (Some((af, ar, a)), Some((bf, br, b))) => {
                    if ar != br {
                        return false;
                    }
                    let (af, a) = fact_operand_identity(af, ar, a);
                    let (bf, b) = fact_operand_identity(bf, br, b);
                    if af != bf {
                        return false;
                    }
                    for (a, b) in a.into_iter().zip(b) {
                        let equal = match (a, b) {
                            (FactOperand::Value(a), FactOperand::Value(b)) => a == b,
                            (FactOperand::Term(a), FactOperand::Term(b)) => machine_equal(a, b),
                            _ => false,
                        };
                        if !equal {
                            return false;
                        }
                    }
                    continue;
                }
                (None, None) => {}
                _ => return false,
            }
            match (left.pointer_offsets(), right.pointer_offsets()) {
                (Some(a), Some(b)) => {
                    if !a.iter().zip(&b).all(|(a, b)| a.syntax_equal(b)) {
                        return false;
                    }
                    continue;
                }
                (None, None) => {}
                _ => return false,
            }
            match (left.pointer_addresses(), right.pointer_addresses()) {
                (Some(a), Some(b)) => {
                    if !a.iter().zip(&b).all(|(a, b)| a.syntax_equal(b)) {
                        return false;
                    }
                    continue;
                }
                (None, None) => {}
                _ => return false,
            }
            if left.identity_leaf() != right.identity_leaf() {
                return false;
            }
        }
        true
    }

    /// Keep numeric call arguments as typed handles for semantic identity.
    /// Other leaves already have exact native payloads or shared Integer
    /// bridges; no enclosing Boolean connective reaches this boundary.
    pub(crate) fn identity_leaf(self) -> std::borrow::Cow<'a, ConditionTerm> {
        if let Self::Shared(root) = self
            && let KernelTermNode::Call { name, arguments } = root.node()
        {
            let mut export = KernelTermExport::default();
            let arguments = arguments
                .iter()
                .map(|argument| {
                    if let KernelType::Program(ty) = argument.ty()
                        && let Some(format) = MachineIntegerType::from_program_type(*ty)
                        && !matches!(argument.node(), KernelTermNode::Legacy(_))
                    {
                        PureFunctionArgument::SharedMachine(
                            MachineOperandView::Shared(argument).retain(format),
                        )
                    } else {
                        export.argument(argument).expect("Boolean call argument")
                    }
                })
                .collect();
            return std::borrow::Cow::Owned(ConditionTerm::BoolApplication(
                SharedPureApplication::intern(name.clone(), arguments),
            ));
        }
        self.native()
    }

    pub(crate) fn native_leaf(self) -> Option<&'a ConditionTerm> {
        match self {
            Self::Native(value) => Some(value),
            Self::Shared(root) => {
                let KernelTermNode::LegacyBool(payload) = root.node() else {
                    return None;
                };
                let PureFunctionArgument::Value(ProgramValue::Bool(MachineTerm::BoolCast {
                    value,
                    ..
                })) = payload.value()
                else {
                    return None;
                };
                Some(value)
            }
        }
    }

    /// Explicit compatibility boundary for callers that still need a native
    /// condition. Borrow existing leaves; only common compound roots export.
    pub(crate) fn native(self) -> std::borrow::Cow<'a, ConditionTerm> {
        if let Some(value) = self.native_leaf() {
            return std::borrow::Cow::Borrowed(value);
        }
        let Self::Shared(root) = self else {
            unreachable!()
        };
        std::borrow::Cow::Owned(KernelTermExport::condition(root).expect("Boolean operand"))
    }

    pub(crate) fn pointer_addresses(self) -> Option<[SharedPointerAddress; 2]> {
        if let Self::Shared(root) = self
            && let KernelTermNode::PointerEqual { arguments } = root.node()
        {
            return Some(arguments.clone());
        }
        let ConditionTerm::PointerEqual(a, b) = self.native_leaf()? else {
            return None;
        };
        Some([
            SharedPointerAddress::import(a),
            SharedPointerAddress::import(b),
        ])
    }

    pub(crate) fn pointer_offsets(self) -> Option<[SharedPointerOffset; 2]> {
        if let Self::Shared(root) = self
            && let KernelTermNode::PointerOffsetEqual { arguments } = root.node()
        {
            return Some(arguments.clone());
        }
        let ConditionTerm::PointerOffsetEqual(a, b) = self.native_leaf()? else {
            return None;
        };
        Some([
            KernelPointerOffset::import(a),
            KernelPointerOffset::import(b),
        ])
    }

    pub(crate) fn constant(self) -> Option<bool> {
        match self {
            Self::Shared(root) if matches!(root.node(), KernelTermNode::BoolLiteral(_)) => {
                let KernelTermNode::BoolLiteral(value) = root.node() else {
                    unreachable!()
                };
                Some(*value)
            }
            _ => match self.native_leaf()? {
                ConditionTerm::Constant(value) => Some(*value),
                _ => None,
            },
        }
    }

    pub(crate) fn conditional(self) -> Option<[Self; 3]> {
        match self {
            Self::Shared(root) => match root.node() {
                KernelTermNode::BoolIf { arguments } => {
                    Some(arguments.each_ref().map(Self::Shared))
                }
                _ => Self::Native(self.native_leaf()?).conditional(),
            },
            Self::Native(ConditionTerm::BoolIf {
                condition,
                then_condition,
                else_condition,
            }) => Some([
                Self::Native(condition),
                Self::Native(then_condition),
                Self::Native(else_condition),
            ]),
            _ => None,
        }
    }

    pub(crate) fn equality(self) -> Option<[Self; 2]> {
        match self {
            Self::Shared(root) => match root.node() {
                KernelTermNode::BoolEqual { arguments } => {
                    Some(arguments.each_ref().map(Self::Shared))
                }
                _ => Self::Native(self.native_leaf()?).equality(),
            },
            Self::Native(ConditionTerm::BoolEqual(left, right)) => {
                Some([Self::Native(left), Self::Native(right)])
            }
            _ => None,
        }
    }

    pub(crate) fn is_integer_comparison(self) -> bool {
        match self {
            Self::Shared(root) if matches!(root.node(), KernelTermNode::IntegerCompare { .. }) => {
                true
            }
            _ => self.native_leaf().is_some_and(|value| {
                matches!(value, crate::kernel::integer_comparison_condition!(_, _))
            }),
        }
    }

    pub(crate) fn is_bool_value_form(self) -> bool {
        match self {
            Self::Shared(root)
                if matches!(
                    root.node(),
                    KernelTermNode::BoolIf { .. }
                        | KernelTermNode::BoolEqual { .. }
                        | KernelTermNode::Call { .. }
                ) =>
            {
                true
            }
            _ => self
                .native_leaf()
                .is_some_and(ConditionTerm::is_bool_value_form),
        }
    }

    pub(crate) fn comparison(
        self,
    ) -> Option<(
        MachineIntegerType,
        CompareRelation,
        [MachineOperandView<'a>; 2],
    )> {
        match self {
            Self::Shared(root) => match root.node() {
                KernelTermNode::BoolCompare {
                    format,
                    relation,
                    arguments,
                } => Some((
                    *format,
                    *relation,
                    arguments.each_ref().map(MachineOperandView::Shared),
                )),
                _ => Self::Native(self.native_leaf()?).comparison(),
            },
            Self::Native(ConditionTerm::Compare {
                format,
                relation,
                left,
                right,
            }) => Some((
                *format,
                *relation,
                [
                    MachineOperandView::Legacy(left),
                    MachineOperandView::Legacy(right),
                ],
            )),
            _ => None,
        }
    }
}

impl KernelTerm {
    pub(crate) fn boolean_if_raw(arguments: [Self; 3]) -> Self {
        Self::intern(KernelType::Bool, KernelTermNode::BoolIf { arguments })
    }

    pub(crate) fn boolean_equal_raw(arguments: [Self; 2]) -> Self {
        Self::intern(KernelType::Bool, KernelTermNode::BoolEqual { arguments })
    }

    /// Structural Boolean reconstruction. The callback owns each selected
    /// atom's existing rewrite and binder rules; connectives are never folded.
    /// A query-local memo prevents shared Boolean prefixes becoming trees.
    pub(crate) fn map_boolean_leaves<E>(
        &self,
        leaf: impl FnMut(&Self) -> Result<Self, E>,
    ) -> Result<Self, E> {
        self.map_boolean_with_connectives(leaf, |original, children| {
            let node = match original.node() {
                KernelTermNode::BoolIf { .. } => KernelTermNode::BoolIf {
                    arguments: [
                        children[0].clone(),
                        children[1].clone(),
                        children[2].clone(),
                    ],
                },
                KernelTermNode::BoolEqual { .. } => KernelTermNode::BoolEqual {
                    arguments: [children[0].clone(), children[1].clone()],
                },
                _ => unreachable!(),
            };
            Ok(Self::intern(KernelType::Bool, node))
        })
    }

    pub(crate) fn map_boolean_with_connectives<E>(
        &self,
        mut leaf: impl FnMut(&Self) -> Result<Self, E>,
        mut connective: impl FnMut(&Self, &[Self]) -> Result<Self, E>,
    ) -> Result<Self, E> {
        let mut rewritten = HashMap::<u64, Self>::new();
        let mut pending = vec![(self, false)];
        while let Some((term, finish)) = pending.pop() {
            if rewritten.contains_key(&term.id()) {
                continue;
            }
            crate::instrumentation::record_deterministic_work(1);
            let children: &[Self] = match term.node() {
                KernelTermNode::BoolIf { arguments } => arguments,
                KernelTermNode::BoolEqual { arguments } => arguments,
                _ => {
                    rewritten.insert(term.id(), leaf(term)?);
                    continue;
                }
            };
            if !finish {
                pending.push((term, true));
                pending.extend(children.iter().rev().map(|child| (child, false)));
                continue;
            }
            let children: Vec<_> = children
                .iter()
                .map(|child| rewritten[&child.id()].clone())
                .collect();
            let result = connective(term, &children)?;
            rewritten.insert(term.id(), result);
        }
        Ok(rewritten
            .remove(&self.id())
            .expect("rewritten Boolean root"))
    }
}

impl KernelTermImport {
    pub(crate) fn condition(&mut self, condition: &ConditionTerm) -> KernelTerm {
        use ConditionTerm as Old;
        use KernelTermNode as Node;
        crate::instrumentation::record_deterministic_work(1);
        let node = match condition {
            Old::PointerEqual(a, b) => Node::PointerEqual {
                arguments: [
                    SharedPointerAddress::import(a),
                    SharedPointerAddress::import(b),
                ],
            },
            Old::PointerOffsetEqual(a, b) => Node::PointerOffsetEqual {
                arguments: [
                    KernelPointerOffset::import(a),
                    KernelPointerOffset::import(b),
                ],
            },
            Old::Constant(value) => Node::BoolLiteral(*value),
            Old::Variable(variable) => Node::Variable(*variable),
            Old::Compare {
                format,
                relation,
                left,
                right,
            } => Node::BoolCompare {
                format: *format,
                relation: *relation,
                arguments: [self.machine(*format, left), self.machine(*format, right)],
            },
            Old::IntegerLessThan(left, right)
            | Old::IntegerLessEqual(left, right)
            | Old::IntegerGreaterThan(left, right)
            | Old::IntegerGreaterEqual(left, right)
            | Old::IntegerEqual(left, right)
            | Old::IntegerNotEqual(left, right) => {
                use IntegerComparisonOperator as Op;
                let operator = match condition {
                    Old::IntegerLessThan(..) => Op::LessThan,
                    Old::IntegerLessEqual(..) => Op::LessEqual,
                    Old::IntegerGreaterThan(..) => Op::GreaterThan,
                    Old::IntegerGreaterEqual(..) => Op::GreaterEqual,
                    Old::IntegerEqual(..) => Op::Equal,
                    Old::IntegerNotEqual(..) => Op::NotEqual,
                    _ => unreachable!(),
                };
                Node::IntegerCompare {
                    operator,
                    arguments: [self.integer(left), self.integer(right)],
                }
            }
            Old::BoolEqual(left, right) => Node::BoolEqual {
                arguments: [self.condition(left), self.condition(right)],
            },
            Old::BoolIf {
                condition,
                then_condition,
                else_condition,
            } => Node::BoolIf {
                arguments: [
                    self.condition(condition),
                    self.condition(then_condition),
                    self.condition(else_condition),
                ],
            },
            Old::BoolApplication(application) => Node::Call {
                name: application.name().into(),
                arguments: application
                    .arguments()
                    .iter()
                    .enumerate()
                    .map(|(index, arg)| match arg {
                        PureFunctionArgument::Integer(_) => self.argument(arg),
                        PureFunctionArgument::Value(integer_c_value!(_))
                        | PureFunctionArgument::SharedMachine(_) => self.argument(arg),
                        _ => KernelTerm::legacy_at(
                            arg.clone(),
                            LegacyIdentity::ApplicationArgument(application.clone(), index),
                        ),
                    })
                    .collect(),
            },
            _ => {
                // Keep the entire condition, including pointer metadata. Do not
                // key this payload by ConditionTerm's semantic equality.
                let leaf = KernelTerm::legacy(PureFunctionArgument::Value(ProgramValue::Bool(
                    MachineTerm::BoolCast {
                        to: MachineIntegerType::UInt8,
                        value: Box::new(condition.clone()),
                    },
                )));
                let Node::Legacy(payload) = leaf.node() else {
                    unreachable!()
                };
                Node::LegacyBool(payload.clone())
            }
        };
        KernelTerm::intern(KernelType::Bool, node)
    }
}

impl KernelTermExport {
    pub(crate) fn condition(term: &KernelTerm) -> Result<ConditionTerm, &'static str> {
        use ConditionTerm as Old;
        use KernelTermNode as Node;
        if term.ty() != &KernelType::Bool {
            return Err("expected Bool kernel term");
        }
        crate::instrumentation::record_deterministic_work(1);
        Ok(match term.node() {
            Node::PointerEqual { arguments: [a, b] } => {
                Old::PointerEqual(Box::new(a.export()?), Box::new(b.export()?))
            }
            Node::PointerOffsetEqual { arguments: [a, b] } => Old::PointerOffsetEqual(
                Box::new(KernelPointerOffset::export(a)?),
                Box::new(KernelPointerOffset::export(b)?),
            ),
            Node::BoolLiteral(value) => Old::Constant(*value),
            Node::Variable(variable) => Old::Variable(*variable),
            Node::BoolCompare {
                format,
                relation,
                arguments,
            } => Old::Compare {
                format: *format,
                relation: *relation,
                left: Box::new(Self::condition_machine_operand(&arguments[0])?),
                right: Box::new(Self::condition_machine_operand(&arguments[1])?),
            },
            Node::IntegerCompare {
                operator,
                arguments,
            } => {
                use IntegerComparisonOperator as Op;
                let mut export = Self::default();
                let left = export.integer(&arguments[0])?;
                let right = export.integer(&arguments[1])?;
                match operator {
                    Op::LessThan => Old::IntegerLessThan(left, right),
                    Op::LessEqual => Old::IntegerLessEqual(left, right),
                    Op::GreaterThan => Old::IntegerGreaterThan(left, right),
                    Op::GreaterEqual => Old::IntegerGreaterEqual(left, right),
                    Op::Equal => Old::IntegerEqual(left, right),
                    Op::NotEqual => Old::IntegerNotEqual(left, right),
                }
            }
            Node::BoolEqual { arguments } => Old::BoolEqual(
                Box::new(Self::condition(&arguments[0])?),
                Box::new(Self::condition(&arguments[1])?),
            ),
            Node::BoolIf { arguments } => Old::BoolIf {
                condition: Box::new(Self::condition(&arguments[0])?),
                then_condition: Box::new(Self::condition(&arguments[1])?),
                else_condition: Box::new(Self::condition(&arguments[2])?),
            },
            Node::Call { name, arguments } => Old::BoolApplication(SharedPureApplication::intern(
                name.clone(),
                arguments
                    .iter()
                    .map(|arg| Self::default().argument(arg))
                    .collect::<Result<Vec<_>, _>>()?,
            )),
            Node::LegacyBool(payload) => {
                let PureFunctionArgument::Value(ProgramValue::Bool(MachineTerm::BoolCast {
                    value,
                    ..
                })) = payload.value()
                else {
                    return Err("expected exact legacy Bool payload");
                };
                *value.clone()
            }
            _ => return Err("expected Bool kernel node"),
        })
    }

    fn condition_machine_operand(term: &KernelTerm) -> Result<MachineTerm, &'static str> {
        // Fixed-size atoms have their exact written form already. Only a
        // compound guard operand needs the remaining Boolean export boundary.
        match term.node() {
            KernelTermNode::Variable(variable) => Ok(MachineTerm::Variable(*variable)),
            KernelTermNode::MachineLiteral(value) => Ok(value.legacy_term()),
            KernelTermNode::MemoryLoad { .. } => {
                Ok(term.machine_read_leaf().expect("read descriptor").clone())
            }
            _ => Self::machine(term),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn boolean_identity_matches_native_formats_and_composites() {
        let _session = crate::kernel::VerificationSession::enter();
        let mut cases = vec![
            ConditionTerm::Constant(false),
            ConditionTerm::Variable(Variable(964_095)),
        ];
        for format in crate::kernel::machine_integer::FORMATS {
            for relation in [
                CompareRelation::Equal,
                CompareRelation::LessThan,
                CompareRelation::GreaterEqual,
            ] {
                cases.push(ConditionTerm::Compare {
                    format,
                    relation,
                    left: Box::new(MachineTerm::Variable(Variable(964_096))),
                    right: Box::new(MachineTerm::machine_constant(
                        MachineIntegerConstant::from_signed(format.format(), 1).unwrap(),
                    )),
                });
            }
        }
        for source in cases.clone() {
            cases.push(ConditionTerm::BoolEqual(
                Box::new(source.clone()),
                Box::new(source),
            ));
        }
        let common: Vec<_> = cases
            .iter()
            .map(|source| KernelTermImport::default().condition(source))
            .collect();
        for (i, a) in cases.iter().enumerate() {
            for (j, b) in cases.iter().enumerate() {
                let expected = a == b;
                let shared_a = BooleanOperandView::Shared(&common[i]);
                let shared_b = BooleanOperandView::Shared(&common[j]);
                assert_eq!(
                    shared_a.syntax_equal(shared_b),
                    expected,
                    "{a:?} versus {b:?}"
                );
                assert_eq!(
                    shared_a.syntax_equal(BooleanOperandView::Native(b)),
                    expected
                );
                assert_eq!(
                    BooleanOperandView::Native(a).syntax_equal(shared_b),
                    expected
                );
            }
        }
    }

    #[test]
    fn common_boolean_substitution_keeps_unfolded_connectives_and_scoped_folds() {
        use crate::kernel::reasoning::substitute_bitvector_variable_in_common_condition;
        let _session = crate::kernel::VerificationSession::enter();
        let free = Variable(971_001);
        let accumulator = Variable(971_002);
        let fold = MachineTerm::RangeFold {
            start: Box::new(MachineTerm::constant(0)),
            end: Box::new(MachineTerm::Variable(free)),
            initial: Box::new(MachineTerm::Variable(accumulator)),
            accumulator,
            item: Variable(971_003),
            body: Box::new(MachineTerm::add(
                MachineTerm::Variable(free),
                MachineTerm::Variable(accumulator),
            )),
        };
        let source = ConditionTerm::BoolIf {
            condition: Box::new(ConditionTerm::Variable(free)),
            then_condition: Box::new(ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left: Box::new(fold.clone()),
                right: Box::new(MachineTerm::Variable(Variable(971_004))),
            }),
            else_condition: Box::new(ConditionTerm::Constant(false)),
        };
        let root = KernelTermImport::default().condition(&source);
        let replacement = MachineTerm::Variable(accumulator);
        let expected =
            crate::kernel::reasoning::substitute_bitvector_variable(&fold, free, &replacement);
        let actual =
            substitute_bitvector_variable_in_common_condition(&root, free, &replacement).unwrap();
        let [_, then_branch, _] = BooleanOperandView::Shared(&actual).conditional().unwrap();
        let (_, _, operands) = then_branch.comparison().unwrap();
        let MachineOperandView::Shared(left) = operands[0] else {
            panic!("common comparison child")
        };
        let actual_fold = KernelTermExport::machine(left).unwrap();
        assert_eq!(
            crate::kernel::proof::fact_keys::bitvector_folds_alpha_equivalent(
                &actual_fold,
                &expected
            ),
            Some(true)
        );
        assert!(matches!(actual.node(), KernelTermNode::BoolIf { .. }));
    }

    #[test]
    fn common_boolean_pointer_substitution_keeps_native_folding_policy() {
        let _session = crate::kernel::VerificationSession::enter();
        let from = Variable(971_020);
        let pointer = Pointer::null();
        let atom = ConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::Equal,
            left: Box::new(MachineTerm::PointerAddress(
                Box::new(Pointer::symbolic(from)),
                crate::kernel::AddressObjectClass::NONE,
            )),
            right: Box::new(MachineTerm::uint64_constant(0)),
        };
        let sources = [
            ConditionTerm::BoolEqual(Box::new(atom.clone()), Box::new(atom.clone())),
            ConditionTerm::BoolIf {
                condition: Box::new(atom),
                then_condition: Box::new(ConditionTerm::Constant(true)),
                else_condition: Box::new(ConditionTerm::Constant(false)),
            },
            ConditionTerm::BoolIf {
                condition: Box::new(ConditionTerm::Constant(true)),
                then_condition: Box::new(ConditionTerm::Variable(Variable(971_021))),
                else_condition: Box::new(ConditionTerm::Constant(false)),
            },
        ];
        for source in sources {
            let expected = crate::kernel::proof::term_rewrite::TermRewrite::for_pointer_variable(
                from, &pointer,
            )
            .condition(&source);
            let root = KernelTermImport::default().condition(&source);
            let actual = crate::kernel::reasoning::substitute_pointer_variable_in_common_condition(
                &root, from, &pointer,
            )
            .unwrap();
            let actual = KernelTermExport::condition(&actual).unwrap();
            assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
        }
    }

    #[test]
    fn common_boolean_pointer_substitution_preserves_read_snapshot() {
        let from = Variable(971_010);
        let memory = crate::kernel::intern_memory(Memory::new());
        let source = ConditionTerm::BoolEqual(
            Box::new(ConditionTerm::BoolLoad(
                memory.clone(),
                Box::new(Pointer::symbolic(from)),
            )),
            Box::new(ConditionTerm::Constant(true)),
        );
        let root = KernelTermImport::default().condition(&source);
        let pointer = Pointer::symbolic(Variable(971_011));
        let actual = crate::kernel::reasoning::substitute_pointer_variable_in_common_condition(
            &root, from, &pointer,
        )
        .unwrap();
        let restored = KernelTermExport::condition(&actual).unwrap();
        assert_eq!(
            restored,
            ConditionTerm::BoolEqual(
                Box::new(ConditionTerm::BoolLoad(memory, Box::new(pointer))),
                Box::new(ConditionTerm::Constant(true)),
            )
        );
    }

    #[test]
    fn boolean_views_keep_written_comparison_and_shared_children() {
        let source = ConditionTerm::BoolIf {
            condition: Box::new(ConditionTerm::Compare {
                format: MachineIntegerType::UInt32,
                relation: CompareRelation::Equal,
                left: Box::new(MachineTerm::Variable(Variable(964_090))),
                right: Box::new(MachineTerm::constant(1)),
            }),
            then_condition: Box::new(ConditionTerm::Constant(true)),
            else_condition: Box::new(ConditionTerm::BoolEqual(
                Box::new(ConditionTerm::Constant(false)),
                Box::new(ConditionTerm::Constant(true)),
            )),
        };
        let common = KernelTermImport::default().condition(&source);
        for view in [
            BooleanOperandView::Native(&source),
            BooleanOperandView::Shared(&common),
        ] {
            let [guard, yes, no] = view.conditional().unwrap();
            let (format, relation, operands) = guard.comparison().unwrap();
            assert_eq!(format, MachineIntegerType::UInt32);
            assert_eq!(relation, CompareRelation::Equal);
            assert_eq!(operands[0].variable(), Some(&Variable(964_090)));
            assert_eq!(yes.constant(), Some(true));
            let [left, right] = no.equality().unwrap();
            assert_eq!(left.constant(), Some(false));
            assert_eq!(right.constant(), Some(true));
            assert_eq!(view.native().as_ref(), &source);
        }
        let [guard, _, _] = BooleanOperandView::Shared(&common).conditional().unwrap();
        assert!(matches!(
            guard.comparison().unwrap().2[0],
            MachineOperandView::Shared(_)
        ));
    }

    #[test]
    fn boolean_view_borrows_exact_legacy_payload() {
        let source = ConditionTerm::PointerEqual(
            Box::new(Pointer::symbolic(Variable(964_091))),
            Box::new(Pointer::symbolic(Variable(964_092))),
        );
        // Test the explicit adapter independently of which condition families
        // have migrated to common producer nodes.
        let native = KernelTerm::legacy(PureFunctionArgument::Value(ProgramValue::Bool(
            MachineTerm::BoolCast {
                to: MachineIntegerType::UInt8,
                value: Box::new(source.clone()),
            },
        )));
        let KernelTermNode::Legacy(payload) = native.node() else {
            panic!("legacy payload")
        };
        let root = KernelTerm::intern(
            KernelType::Bool,
            KernelTermNode::LegacyBool(payload.clone()),
        );
        let view = BooleanOperandView::Shared(&root);
        assert!(matches!(view.native(), std::borrow::Cow::Borrowed(_)));
        assert_eq!(view.native_leaf(), Some(&source));
        assert!(view.conditional().is_none());
        assert!(view.comparison().is_none());
    }

    #[test]
    fn integer_comparisons_preserve_all_operators_and_order_after_source_drop() {
        use IntegerComparisonOperator as Op;
        type Constructor = fn(SharedIntegerTerm, SharedIntegerTerm) -> ConditionTerm;
        let constructors: [(Op, Constructor); 6] = [
            (Op::LessThan, ConditionTerm::IntegerLessThan),
            (Op::LessEqual, ConditionTerm::IntegerLessEqual),
            (Op::GreaterThan, ConditionTerm::IntegerGreaterThan),
            (Op::GreaterEqual, ConditionTerm::IntegerGreaterEqual),
            (Op::Equal, ConditionTerm::IntegerEqual),
            (Op::NotEqual, ConditionTerm::IntegerNotEqual),
        ];
        let mut distinct = std::collections::HashSet::new();
        for (operator, constructor) in constructors {
            let left: SharedIntegerTerm = IntegerTerm::Add(
                IntegerTerm::Variable(Variable(964_001)).into(),
                IntegerTerm::constant_i64(1).into(),
            )
            .into();
            let right: SharedIntegerTerm = IntegerTerm::constant_i64(0).into();
            let source = constructor(left, right);
            let term = KernelTermImport::default().condition(&source);
            assert_eq!(term.ty(), &KernelType::Bool);
            assert!(
                matches!(term.node(), KernelTermNode::IntegerCompare { operator: actual, .. } if *actual == operator)
            );
            assert_eq!(term.children().len(), 2);
            assert!(
                term.children()
                    .iter()
                    .all(|child| child.ty() == &KernelType::Integer)
            );
            assert!(matches!(
                term.children()[0].node(),
                KernelTermNode::IntegerOperation { .. }
            ));
            assert!(matches!(
                term.children()[1].node(),
                KernelTermNode::IntegerLiteral(_)
            ));
            assert!(distinct.insert(term.clone()));
            assert_eq!(KernelTermImport::default().condition(&source), term);
            drop(source);
            let restored = KernelTermExport::condition(&term).unwrap();
            // Reconstructed old objects may have new allocation IDs; the
            // common operator and ordered operands must retain their identity.
            assert_eq!(KernelTermImport::default().condition(&restored), term);
        }
    }

    #[test]
    fn boolean_bridge_preserves_structure_and_comparison_format() {
        let comparison = |format| ConditionTerm::Compare {
            format,
            relation: CompareRelation::Equal,
            left: Box::new(MachineTerm::Variable(Variable(961_001))),
            right: Box::new(MachineTerm::constant(0)),
        };
        let signed = comparison(MachineIntegerType::Int32);
        let unsigned = comparison(MachineIntegerType::UInt32);
        // Fact equality deliberately identifies these. Term identity must not.
        assert_eq!(signed, unsigned);
        assert_ne!(
            KernelTermImport::default().condition(&signed),
            KernelTermImport::default().condition(&unsigned)
        );
        for condition in [
            signed,
            unsigned,
            ConditionTerm::Constant(false),
            ConditionTerm::Variable(Variable(961_002)),
            ConditionTerm::BoolEqual(
                Box::new(ConditionTerm::Constant(true)),
                Box::new(ConditionTerm::Constant(true)),
            ),
            ConditionTerm::BoolIf {
                condition: Box::new(ConditionTerm::Constant(false)),
                then_condition: Box::new(ConditionTerm::Constant(true)),
                else_condition: Box::new(ConditionTerm::Constant(false)),
            },
            ConditionTerm::BoolApplication(SharedPureApplication::intern(
                "predicate".into(),
                vec![PureFunctionArgument::Value(ProgramValue::Int32(
                    MachineTerm::Variable(Variable(961_003)),
                ))],
            )),
            ConditionTerm::IntegerEqual(
                IntegerTerm::constant_i64(1).into(),
                IntegerTerm::constant_i64(2).into(),
            ),
        ] {
            for destination in [
                MachineIntegerType::Int8,
                MachineIntegerType::Int32,
                MachineIntegerType::UInt64,
                MachineIntegerType::UInt128,
            ] {
                let source = PureFunctionArgument::Value(super::super::machine::wrap_exact(
                    destination,
                    MachineTerm::BoolCast {
                        to: destination,
                        value: Box::new(condition.clone()),
                    },
                ));
                let term = KernelTermImport::default().argument(&source);
                assert!(matches!(term.node(), KernelTermNode::BoolCast { .. }));
                assert_eq!(term.children()[0].ty(), &KernelType::Bool);
                let restored = KernelTermExport::default().argument(&term).unwrap();
                // Debug retains the comparison format that equality omits.
                assert_eq!(format!("{restored:?}"), format!("{source:?}"));
            }
        }
    }
}
