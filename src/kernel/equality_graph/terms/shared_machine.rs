//! Register the native shared native fragment without exporting boxed prefixes.
//! The operator nodes are the same nodes used by legacy congruence registration.
use super::*;
use crate::kernel::{
    Bitvector32Term as T, BitvectorBinaryOp as B, CarrierWidth as W, KernelMachineLiteral as L,
    KernelTerm, KernelTermNode as N,
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
            let class = match term.node() {
                N::MachineBinary {
                    format,
                    operator,
                    arguments: [left, right],
                } => {
                    let opaque_count = width != W::Bits32
                        && matches!(
                            operator,
                            MachineBinaryOp::ShiftLeft | MachineBinaryOp::ShiftRight
                        );
                    if !finish {
                        pending.push((term, true));
                        if !opaque_count {
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
                    let b = if opaque_count {
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
                    let equivalent = if width == W::Bits64 {
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
                                        T::Int64Constant(0)
                                    } else {
                                        T::UInt64Constant(0)
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
                        && matches!(width, W::Bits32 | W::Bits64)
                        && format == inner_format
                        && matches!(
                            (operator, inner_op),
                            (MachineBinaryOp::Add, MachineBinaryOp::Subtract)
                                | (MachineBinaryOp::Subtract, MachineBinaryOp::Add)
                        )
                        && matches!(added.node(), N::MachineLiteral(_))
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
                    if !finish {
                        pending.push((term, true));
                        pending.push((operand, false));
                        continue;
                    }
                    let value = self
                        .shared_machine_classes
                        .get(&(operand.id(), width))
                        .unwrap()
                        .1;
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
                // Leaves retain load-name registration and literal normalization.
                N::Variable(variable) => self.intern_typed_machine(&T::Variable(*variable), width),
                N::MachineLiteral(_) => {
                    let literal =
                        crate::kernel::KernelTermExport::machine(term).expect("literal leaf");
                    self.intern_typed_machine(&literal, width)
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
}
