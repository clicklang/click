//! Register shared machine operands without exporting boxed prefixes.
//! The operator nodes are the same nodes used by legacy congruence registration.
use super::*;
use crate::kernel::MachineCastSpelling;
use crate::kernel::{
    BitvectorBinaryOp as B, CarrierWidth as W, KernelMachineLiteral as L, KernelTerm,
    KernelTermNode as N, MachineTerm as T,
};

impl TermClasses {
    pub(super) fn intern_shared_machine(&mut self, term: &KernelTerm, width: W) -> u64 {
        let mut pending = vec![(term, false)];
        while let Some((term, finish)) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            let key = (term.id(), width);
            if self.shared_machine_classes.contains_key(&key) {
                continue;
            }
            // The observation may read an operator at another carrier width.
            // Legacy registration keeps such an operator opaque (except for
            // its explicit add/sub cancellation). Retain that exact identity
            // without exporting the operator's shared descendants.
            let operator_format = match term.node() {
                N::MachineBinary { format, .. } | N::MachineUnary { format, .. } => Some(*format),
                _ => None,
            };
            if operator_format.is_some_and(|format| {
                let native = if format.format().bits() == 128 {
                    W::Bits64
                } else {
                    W::of_machine_type(format)
                };
                native != width
                    && !matches!(
                        (term.node(), width),
                        (
                            N::MachineUnary {
                                format: MachineIntegerType::UInt32,
                                ..
                            },
                            W::Bits64
                        )
                    )
            }) {
                let cancellation = match term.node() {
                    N::MachineBinary {
                        format,
                        operator,
                        arguments: [left, right],
                    } if matches!(format.format().bits(), 32 | 64) => match left.node() {
                        N::MachineBinary {
                            format: inner_format,
                            operator: inner_op,
                            arguments: [base, added],
                        } if format == inner_format
                            && matches!(
                                (operator, inner_op),
                                (MachineBinaryOp::Add, MachineBinaryOp::Subtract)
                                    | (MachineBinaryOp::Subtract, MachineBinaryOp::Add)
                            )
                            && matches!(
                                added.node(),
                                N::MachineLiteral(
                                    L::Word32(_) | L::UInt32(_) | L::Int64(_) | L::UInt64(_)
                                )
                            )
                            && added == right =>
                        {
                            Some(base)
                        }
                        _ => None,
                    },
                    _ => None,
                };
                let class = if let Some(base) = cancellation {
                    if !finish {
                        pending.push((term, true));
                        pending.push((base, false));
                        continue;
                    }
                    self.shared_machine_classes
                        .get(&(base.id(), width))
                        .unwrap()
                        .1
                } else {
                    let format = match width {
                        W::Bits8 => MachineIntegerType::UInt8,
                        W::Bits16 => MachineIntegerType::UInt16,
                        W::Bits32 => MachineIntegerType::Int32,
                        W::Bits64 => MachineIntegerType::UInt64,
                        W::Bits128 => MachineIntegerType::UInt128,
                    };
                    let atom = MachineAtom::from_operand(
                        format,
                        crate::kernel::MachineOperandView::Shared(term),
                    );
                    self.intern_node(match width {
                        W::Bits8 | W::Bits16 => Node::MachineNarrow(atom),
                        W::Bits32 => Node::Int32(atom),
                        W::Bits64 => Node::UInt64(atom),
                        W::Bits128 => Node::Machine128(atom),
                    })
                };
                self.shared_machine_classes
                    .insert(key, (term.clone(), class));
                continue;
            }
            let class = match term.node() {
                N::MachineBinary {
                    format,
                    operator,
                    arguments: [left, right],
                } => {
                    // A native narrow left shift's count is a 32-bit word,
                    // as the legacy registration interns it (rule N).
                    let word_count = matches!(width, W::Bits8 | W::Bits16)
                        && *operator == MachineBinaryOp::ShiftLeft;
                    let opaque_count = width != W::Bits32
                        && format.format().bits() != 128
                        && !word_count
                        && matches!(
                            operator,
                            MachineBinaryOp::ShiftLeft | MachineBinaryOp::ShiftRight
                        );
                    if !finish {
                        pending.push((term, true));
                        if !opaque_count && !word_count {
                            pending.push((right, false));
                        }
                        pending.push((left, false));
                        continue;
                    }
                    let a = self
                        .shared_machine_classes
                        .get(&(left.id(), width))
                        .unwrap()
                        .1;
                    let b = if word_count {
                        // One more registration at 32 bits, where a narrow
                        // operator is opaque, so the recursion stops there.
                        self.intern_shared_machine(right, W::Bits32)
                    } else if opaque_count {
                        let operand = crate::kernel::SharedMachineIntegerTerm::from_shared(
                            MachineIntegerType::UInt64,
                            right.with_machine_observation_type(MachineIntegerType::UInt64),
                        )
                        .expect("shared count");
                        self.intern_node(Node::OpaqueMachineCount(MachineAtom(operand)))
                    } else {
                        self.shared_machine_classes
                            .get(&(right.id(), width))
                            .unwrap()
                            .1
                    };
                    // Reuse the selected operands' current classes. Keeping
                    // old alias IDs here would create a fresh congruent node
                    // for every `(x + 0) + 0` prefix and repeatedly merge the
                    // growing class's parent uses.
                    let (a, b) = if width == W::Bits32 {
                        (self.root(a), self.root(b))
                    } else {
                        (a, b)
                    };
                    let node = if width == W::Bits32 {
                        match (*format, *operator) {
                            (_, MachineBinaryOp::Add) => Node::Int32Add(a, b),
                            (_, MachineBinaryOp::BitwiseXor) => {
                                Node::Int32Binary(Int32Binary::BitwiseXor, a, b)
                            }
                            (MachineIntegerType::UInt32, MachineBinaryOp::Divide) => {
                                Node::Int32Binary(Int32Binary::UnsignedDivide, a, b)
                            }
                            (MachineIntegerType::UInt32, MachineBinaryOp::Remainder) => {
                                Node::Int32Binary(Int32Binary::UnsignedRemainder, a, b)
                            }
                            _ => Node::Int32Binary(
                                Int32Binary::Other(word_operator(B::Machine(*format, *operator))),
                                a,
                                b,
                            ),
                        }
                    } else if *format == MachineIntegerType::UInt64 && !opaque_count {
                        let op = match operator {
                            MachineBinaryOp::Add => UInt64Binary::Add,
                            MachineBinaryOp::Subtract => UInt64Binary::Subtract,
                            MachineBinaryOp::Multiply => UInt64Binary::Multiply,
                            MachineBinaryOp::Divide => UInt64Binary::Divide,
                            MachineBinaryOp::Remainder => UInt64Binary::Remainder,
                            MachineBinaryOp::BitwiseAnd => UInt64Binary::And,
                            MachineBinaryOp::BitwiseOr => UInt64Binary::Or,
                            MachineBinaryOp::BitwiseXor => UInt64Binary::Xor,
                            _ => unreachable!("non-shift operator"),
                        };
                        Node::UInt64Binary(op, a, b)
                    } else {
                        let head = self.intern_node(Node::MachineBinary(
                            B::Machine(*format, *operator),
                            width,
                        ));
                        let partial = self.intern_node(Node::Apply(head, a));
                        Node::Apply(partial, b)
                    };
                    let class = self.intern_node(node);
                    // Preserve the literal word identities of the legacy
                    // registration path, solely as graph equalities.
                    let number = |t: &KernelTerm, n| {
                        matches!(t.node(),
                        N::MachineLiteral(L::Int64(v)) if *v == n)
                            || matches!(t.node(), N::MachineLiteral(L::UInt64(v)) if *v == n as u64)
                    };
                    let equivalent = if width == W::Bits64
                        && matches!(
                            format,
                            MachineIntegerType::Int64 | MachineIntegerType::UInt64
                        ) {
                        match operator {
                            MachineBinaryOp::Add if number(left, 0) => Some(b),
                            MachineBinaryOp::Add | MachineBinaryOp::Subtract
                                if number(right, 0) =>
                            {
                                Some(a)
                            }
                            MachineBinaryOp::Multiply if number(left, 0) || number(right, 1) => {
                                Some(a)
                            }
                            MachineBinaryOp::Multiply if number(right, 0) || number(left, 1) => {
                                Some(b)
                            }
                            MachineBinaryOp::Subtract if left == right => {
                                Some(self.intern_typed_machine(
                                    &if *format == MachineIntegerType::Int64 {
                                        T::int64_constant(0)
                                    } else {
                                        T::uint64_constant(0)
                                    },
                                    width,
                                ))
                            }
                            _ => None,
                        }
                    } else {
                        None
                    };
                    if let Some(other) = equivalent {
                        self.close(vec![(class, other)]);
                    }
                    if let N::MachineBinary {
                        format: inner_format,
                        operator: inner_op,
                        arguments: [base, added],
                    } = left.node()
                        && matches!(format.format().bits(), 32 | 64)
                        && format == inner_format
                        && matches!(
                            (operator, inner_op),
                            (MachineBinaryOp::Add, MachineBinaryOp::Subtract)
                                | (MachineBinaryOp::Subtract, MachineBinaryOp::Add)
                        )
                        && matches!(
                            added.node(),
                            N::MachineLiteral(
                                L::Word32(_) | L::UInt32(_) | L::Int64(_) | L::UInt64(_)
                            )
                        )
                        && added == right
                    {
                        let other = self
                            .shared_machine_classes
                            .get(&(base.id(), width))
                            .unwrap()
                            .1;
                        self.close(vec![(class, other)]);
                    }
                    class
                }
                N::MachineUnary {
                    format,
                    operator,
                    operand,
                } => {
                    let source_width = W::of_machine_type(*format);
                    let value = if source_width != width {
                        // The legacy wide query of a uint32 complement (and
                        // its raw 128-bit counterpart) reads its own-width
                        // operand. This transition cannot recurse at that
                        // same mismatched root width.
                        self.intern_shared_machine(operand, source_width)
                    } else {
                        if !finish {
                            pending.push((term, true));
                            pending.push((operand, false));
                            continue;
                        }
                        self.shared_machine_classes
                            .get(&(operand.id(), width))
                            .unwrap()
                            .1
                    };
                    if width == W::Bits32 {
                        self.intern_node(Node::Int32Unary(Int32Unary::Not, value))
                    } else {
                        let head = self.intern_node(Node::MachineUnary(
                            crate::kernel::BitvectorUnaryOp::Machine(*format, *operator),
                            width,
                        ));
                        self.intern_node(Node::Apply(head, value))
                    }
                }
                N::MachineCast {
                    encoding,
                    source,
                    destination,
                    operand,
                } => {
                    use MachineCastSpelling::Generic;
                    let generic = *encoding == Generic;
                    let native = W::of_machine_type(*destination);
                    let narrow = generic
                        && width == native
                        && destination.format().bits() < 32
                        && source.format().bits() <= 64;
                    let word = generic
                        && width == W::Bits32
                        && source.format().bits() <= 32
                        && destination.format().bits() <= 32;
                    if narrow || word || width == native {
                        let value =
                            self.intern_shared_machine(operand, W::of_machine_type(*source));
                        let inverse = generic
                            && *source == MachineIntegerType::UInt8
                            && *destination == MachineIntegerType::Int8
                            && crate::kernel::MachineOperandView::Shared(operand)
                                .read_source()
                                .is_some_and(|operand| {
                                    matches!(
                                        crate::kernel::eval::viewed_as_memory_load(&operand),
                                        Some(T::MemoryLoad(_, _, crate::kernel::LoadKind::UInt8))
                                    )
                                });
                        if narrow {
                            self.narrow_cast_node(*source, *destination, value, inverse)
                        } else if word {
                            let op = Int32Unary::Cast(*source, *destination);
                            let node = self.intern_node(Node::Int32Unary(op, value));
                            if inverse {
                                self.register_byte_inverse(node, value);
                            }
                            node
                        } else {
                            let head = self.intern_node(Node::MachineUnary(
                                encoding.unary(*source, *destination),
                                width,
                            ));
                            self.intern_node(Node::Apply(head, value))
                        }
                    } else {
                        let format = match width {
                            W::Bits8 => MachineIntegerType::UInt8,
                            W::Bits16 => MachineIntegerType::UInt16,
                            W::Bits32 => MachineIntegerType::Int32,
                            W::Bits64 => MachineIntegerType::UInt64,
                            W::Bits128 => MachineIntegerType::UInt128,
                        };
                        let atom = MachineAtom::from_operand(
                            format,
                            crate::kernel::MachineOperandView::Shared(term),
                        );
                        self.intern_node(match width {
                            W::Bits8 | W::Bits16 => Node::MachineNarrow(atom),
                            W::Bits32 => Node::Int32(atom),
                            W::Bits64 => Node::UInt64(atom),
                            W::Bits128 => Node::Machine128(atom),
                        })
                    }
                }
                // Leaves retain load-name registration and literal normalization.
                N::MemoryLoad { .. } => {
                    // Match native graph registration at the selected leaf;
                    // never export the surrounding shared expression.
                    let format = match width {
                        W::Bits8 => MachineIntegerType::UInt8,
                        W::Bits16 => MachineIntegerType::UInt16,
                        W::Bits32 => MachineIntegerType::Int32,
                        W::Bits64 => MachineIntegerType::UInt64,
                        W::Bits128 => MachineIntegerType::UInt128,
                    };
                    if width == W::Bits64 {
                        self.intern_typed_machine(
                            term.machine_read_leaf().expect("read leaf"),
                            width,
                        )
                    } else if width != W::Bits128 && {
                        let (memory, pointer, kind) =
                            crate::kernel::MachineOperandView::Shared(term)
                                .read()
                                .expect("read descriptor");
                        crate::kernel::eval::is_selected_scalar_read(memory, pointer, kind)
                    } {
                        let atom = MachineAtom::from_operand(
                            format,
                            crate::kernel::MachineOperandView::Shared(term),
                        );
                        self.intern_node(match width {
                            W::Bits8 | W::Bits16 => Node::MachineNarrow(atom),
                            W::Bits32 => Node::Int32(atom),
                            _ => unreachable!(),
                        })
                    } else {
                        // The graph uses the same assumption-free read identity
                        // as its native entry point. Keep the written descriptor
                        // intact; only its graph class follows that identity.
                        let canonical = crate::kernel::canonical_term(
                            term.machine_read_leaf().expect("read leaf"),
                        );
                        let shared = crate::kernel::KernelTermImport::default()
                            .machine_arithmetic(format, &canonical);
                        if let Some(shared) = shared {
                            if shared != term.with_machine_observation_type(format) {
                                self.intern_shared_machine(&shared, width)
                            } else {
                                let atom = MachineAtom::from_operand(
                                    format,
                                    crate::kernel::MachineOperandView::Shared(term),
                                );
                                self.intern_node(match width {
                                    W::Bits8 | W::Bits16 => Node::MachineNarrow(atom),
                                    W::Bits32 => Node::Int32(atom),
                                    W::Bits128 => Node::Machine128(atom),
                                    W::Bits64 => unreachable!(),
                                })
                            }
                        } else {
                            // A stored value can belong to a native-only term
                            // family even when its read has a shared descriptor.
                            self.intern_typed_machine(&canonical, width)
                        }
                    }
                }
                N::IntegerToMachine { .. } | N::Legacy(_) => self.intern_typed_machine(
                    term.machine_conversion_leaf().expect("conversion leaf"),
                    width,
                ),
                N::Variable(variable) => self.intern_typed_machine(&T::Variable(*variable), width),
                N::MachineLiteral(value) => {
                    crate::instrumentation::record_deterministic_work(1);
                    self.intern_typed_machine(&value.legacy_term(), width)
                }
                _ => unreachable!("cached shared native fragment"),
            };
            self.shared_machine_classes
                .insert(key, (term.clone(), class));
        }
        self.shared_machine_classes
            .get(&(term.id(), width))
            .unwrap()
            .1
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{IntegerTerm, KernelTermImport, SharedMachineIntegerTerm};

    #[test]
    fn comparison_nodes_match_legacy_across_formats_and_merges() {
        use crate::kernel::{CompareRelation as R, ConditionTerm, MachineOperandView as V};
        for format in crate::kernel::machine_integer::FORMATS {
            for relation in [
                R::Equal,
                R::LessThan,
                R::LessEqual,
                R::GreaterThan,
                R::GreaterEqual,
            ] {
                let _session = crate::kernel::VerificationSession::enter();
                let variable = T::Variable(Variable(982410));
                let other = T::Variable(Variable(982411));
                let left = T::Binary {
                    format,
                    op: MachineBinaryOp::Add,
                    left: Box::new(variable.clone()),
                    right: Box::new(other.clone()),
                };
                let mut import = KernelTermImport::default();
                let shared_left = import.machine(format, &left);
                let shared_right = import.machine(format, &other);
                let condition = ConditionTerm::Compare {
                    format,
                    relation,
                    left: Box::new(left),
                    right: Box::new(other.clone()),
                };
                let mut classes = TermClasses::default();
                let a = classes.machine_comparison_node(
                    format,
                    relation,
                    [V::Shared(&shared_left), V::Shared(&shared_right)],
                );
                let b = classes.condition_node(&condition);
                assert_eq!(a, b, "{format:?} {relation:?}");
                for truth in [false, true] {
                    let operands = [V::Shared(&shared_left), V::Shared(&shared_right)];
                    let mut admitted_shared = TermClasses::default();
                    let mut admitted_legacy = TermClasses::default();
                    assert_eq!(
                        admitted_shared.admit_machine_comparison(format, relation, operands, truth),
                        a.is_some()
                    );
                    assert_eq!(
                        admitted_legacy.admit_condition(&condition, truth),
                        a.is_some()
                    );
                    assert_eq!(
                        admitted_shared.knows_condition(&condition, truth),
                        a.is_some()
                    );
                    assert_eq!(
                        admitted_legacy.knows_machine_comparison(format, relation, operands, truth),
                        a.is_some()
                    );
                    assert!(!admitted_shared.knows_condition(&condition, !truth));
                    assert!(
                        !admitted_legacy
                            .knows_machine_comparison(format, relation, operands, !truth)
                    );
                }

                classes.add_typed_equality(W::of_machine_type(format), &variable, &other);
                let again = classes.machine_comparison_node(
                    format,
                    relation,
                    [V::Shared(&shared_left), V::Shared(&shared_right)],
                );
                assert_eq!(a.map(|n| classes.root(n)), again.map(|n| classes.root(n)));
            }
        }
    }

    #[test]
    fn shared_registration_preserves_cross_width_opaque_identities() {
        for format in crate::kernel::machine_integer::FORMATS {
            let variable = T::Variable(Variable(982401));
            let literal = if format.format().bits() <= 32 {
                T::constant(1)
            } else {
                T::uint64_constant(1)
            };
            let child = T::Binary {
                format: MachineIntegerType::UInt32,
                op: MachineBinaryOp::Add,
                left: Box::new(variable.clone()),
                right: Box::new(literal.clone()),
            };
            for op in [
                MachineBinaryOp::Add,
                MachineBinaryOp::Subtract,
                MachineBinaryOp::Multiply,
                MachineBinaryOp::ShiftRight,
            ] {
                for left in [variable.clone(), child.clone()] {
                    let term = T::Binary {
                        format,
                        op,
                        left: Box::new(left),
                        right: Box::new(literal.clone()),
                    };
                    let cancellation = T::Binary {
                        format,
                        op: MachineBinaryOp::Subtract,
                        left: Box::new(T::Binary {
                            format,
                            op: MachineBinaryOp::Add,
                            left: Box::new(term.clone()),
                            right: Box::new(literal.clone()),
                        }),
                        right: Box::new(literal.clone()),
                    };
                    let complement = T::Unary {
                        format,
                        op: crate::kernel::MachineUnaryOp::BitwiseNot,
                        operand: Box::new(term.clone()),
                    };
                    for boxed in [term, cancellation, complement] {
                        let shared = KernelTermImport::default().machine(format, &boxed);
                        for observed in [
                            MachineIntegerType::UInt8,
                            MachineIntegerType::UInt16,
                            MachineIntegerType::Int32,
                            MachineIntegerType::UInt64,
                            MachineIntegerType::UInt128,
                        ] {
                            let _session = crate::kernel::VerificationSession::enter();
                            let width = W::of_machine_type(observed);
                            let observation = SharedMachineIntegerTerm::from_shared(
                                observed,
                                shared.with_machine_observation_type(observed),
                            )
                            .unwrap();
                            let mut classes = TermClasses::default();
                            let a = classes.intern_shared_machine(
                                observation.shared_operand().unwrap(),
                                width,
                            );
                            classes.intern_integer(&IntegerTerm::Machine(observation.clone()));
                            assert!(!observation.has_boxed_operand());
                            let b = classes.intern_typed_machine(&boxed, width);
                            assert_eq!(classes.root(a), classes.root(b), "{observed:?}: {boxed:?}");
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn shared_machine_registration_meets_legacy_classes_and_late_merges() {
        let _session = crate::kernel::VerificationSession::enter();
        for format in [
            MachineIntegerType::Int8,
            MachineIntegerType::UInt8,
            MachineIntegerType::Int16,
            MachineIntegerType::UInt16,
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ] {
            let width = W::of_machine_type(format);
            let variable = |id| T::Variable(Variable(id));
            let constant = |n: i32| {
                format
                    .constant_term(
                        crate::kernel::MachineIntegerConstant::from_integer(
                            format.format(),
                            &n.into(),
                        )
                        .unwrap(),
                    )
                    .unwrap()
            };
            for op in [
                MachineBinaryOp::Add,
                MachineBinaryOp::Subtract,
                MachineBinaryOp::Multiply,
                MachineBinaryOp::Divide,
                MachineBinaryOp::Remainder,
                MachineBinaryOp::ShiftLeft,
                MachineBinaryOp::ShiftRight,
                MachineBinaryOp::BitwiseAnd,
                MachineBinaryOp::BitwiseOr,
                MachineBinaryOp::BitwiseXor,
            ] {
                for right in [variable(981001), constant(0), constant(1)] {
                    let boxed = T::Binary {
                        format,
                        op,
                        left: Box::new(variable(981000)),
                        right: Box::new(right),
                    };
                    let shared = KernelTermImport::default().machine(format, &boxed);
                    let observation =
                        SharedMachineIntegerTerm::from_shared(format, shared.clone()).unwrap();
                    let mut classes = TermClasses::default();
                    let a = classes.intern_shared_machine(&shared, width);
                    assert!(!observation.has_boxed_operand());
                    let b = classes.intern_typed_machine(&boxed, width);
                    assert_eq!(classes.root(a), classes.root(b));
                    let observed = IntegerTerm::Machine(observation);
                    classes.intern_integer(&observed);
                    classes.add_typed_equality(width, &variable(981000), &constant(3));
                    let mut replaced = boxed.clone();
                    let T::Binary { left, .. } = &mut replaced else {
                        unreachable!()
                    };
                    *left = Box::new(constant(3));
                    let after = classes.intern_typed_machine(&replaced, width);
                    let again = classes.intern_shared_machine(&shared, width);
                    assert_eq!(classes.root(after), classes.root(again));
                }
            }
        }
    }
    #[test]
    fn shared_cast_registration_matches_legacy_across_widths() {
        use crate::kernel::machine_integer::FORMATS;
        let _session = crate::kernel::VerificationSession::enter();
        for source in FORMATS {
            for destination in FORMATS {
                let boxed = T::Cast {
                    spelling: MachineCastSpelling::Generic,
                    from: source,
                    to: destination,
                    value: Box::new(T::Variable(Variable(985101))),
                };
                let root = KernelTermImport::default()
                    .machine_arithmetic(destination, &boxed)
                    .unwrap();
                for observed in [
                    MachineIntegerType::UInt8,
                    MachineIntegerType::UInt16,
                    MachineIntegerType::Int32,
                    MachineIntegerType::UInt64,
                    MachineIntegerType::UInt128,
                ] {
                    let width = W::of_machine_type(observed);
                    let observation = SharedMachineIntegerTerm::from_shared(
                        observed,
                        root.with_machine_observation_type(observed),
                    )
                    .unwrap();
                    let mut classes = TermClasses::default();
                    let shared =
                        classes.intern_shared_machine(observation.shared_operand().unwrap(), width);
                    assert!(!observation.has_boxed_operand());
                    let legacy = classes.intern_typed_machine(&boxed, width);
                    assert_eq!(
                        classes.root(shared),
                        classes.root(legacy),
                        "{source:?} -> {destination:?} at {observed:?}"
                    );
                }
            }
        }
    }

    mod scaling_tests {
        include!("../../../scaling_tests/kernel/equality_graph/terms/shared_machine/tests.rs");
    }
}
