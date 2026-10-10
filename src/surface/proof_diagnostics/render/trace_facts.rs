//! Typed diagnostic forms for facts without an exact source spelling.
use super::*;

impl Renderer<'_> {
    pub(super) fn resource_arguments(&mut self, arguments: &[AlgebraicValue]) {
        self.push("(");
        for (index, argument) in arguments.iter().enumerate() {
            if !self.visit() {
                break;
            }
            if index > 0 {
                self.push(", ");
            }
            self.algebraic_value(argument);
        }
        self.push(")");
    }

    pub(super) fn resource_composition(&mut self, context: &crate::kernel::ResourceContext) {
        const LIMIT: usize = 8;
        let (count, entries) = context.diagnostic_facts(LIMIT);
        self.push("validated-composition { ");
        for (index, fact) in entries.enumerate() {
            if !self.visit() {
                break;
            }
            if index > 0 {
                self.push("; ");
            }
            match fact {
                CResourceFact::Own(resource, quantity) => {
                    self.push("owns ");
                    self.resource(resource);
                    self.push(" x ");
                    self.bitvector(quantity);
                }
                CResourceFact::View(resource) => {
                    self.push("views ");
                    self.resource(resource);
                }
            }
        }
        if count > LIMIT {
            self.fmt(format_args!(
                "; … {} more entries (context display limit)",
                count - LIMIT
            ));
        }
        self.push("; support details omitted }");
    }

    /// Spell the operator as well as its numeric interpretation. A shared
    /// term arena does not make signed/unsigned or 32/64-bit operations equal.
    pub(super) fn machine_operation(&mut self, value: &Bitvector32Term) -> bool {
        use Bitvector32Term::*;
        let binary = match value {
            Divide(a, b) => Some((a, b, "bits32", "sdiv")),
            UnsignedDivide(a, b) => Some((a, b, "bits32", "udiv")),
            Remainder(a, b) => Some((a, b, "bits32", "srem")),
            UnsignedRemainder(a, b) => Some((a, b, "bits32", "urem")),
            ShiftLeft(a, b) => Some((a, b, "bits32", "<<")),
            ArithmeticShiftRight(a, b) => Some((a, b, "bits32", "ashr")),
            LogicalShiftRight(a, b) => Some((a, b, "bits32", "lshr")),
            BitwiseAnd(a, b) => Some((a, b, "bits32", "&")),
            BitwiseOr(a, b) => Some((a, b, "bits32", "|")),
            BitwiseXor(a, b) => Some((a, b, "bits32", "^")),
            Int64Add(a, b) => Some((a, b, "int64", "+")),
            Int64Subtract(a, b) => Some((a, b, "int64", "-")),
            Int64Multiply(a, b) => Some((a, b, "int64", "*")),
            Int64Divide(a, b) => Some((a, b, "int64", "/")),
            Int64Remainder(a, b) => Some((a, b, "int64", "%")),
            Int64ShiftLeft(a, b) => Some((a, b, "int64", "<<")),
            Int64ArithmeticShiftRight(a, b) => Some((a, b, "int64", ">>")),
            Int64BitwiseAnd(a, b) => Some((a, b, "int64", "&")),
            Int64BitwiseOr(a, b) => Some((a, b, "int64", "|")),
            Int64BitwiseXor(a, b) => Some((a, b, "int64", "^")),
            UInt64Add(a, b) => Some((a, b, "uint64", "+")),
            UInt64Subtract(a, b) => Some((a, b, "uint64", "-")),
            UInt64Multiply(a, b) => Some((a, b, "uint64", "*")),
            UInt64Divide(a, b) => Some((a, b, "uint64", "/")),
            UInt64Remainder(a, b) => Some((a, b, "uint64", "%")),
            UInt64ShiftLeft(a, b) => Some((a, b, "uint64", "<<")),
            UInt64LogicalShiftRight(a, b) => Some((a, b, "uint64", ">>")),
            UInt64BitwiseAnd(a, b) => Some((a, b, "uint64", "&")),
            UInt64BitwiseOr(a, b) => Some((a, b, "uint64", "|")),
            UInt64BitwiseXor(a, b) => Some((a, b, "uint64", "^")),
            _ => None,
        };
        if let Some((a, b, kind, operator)) = binary {
            self.push(kind);
            self.push("(");
            self.binary_bv(operator, a, b);
            self.push(")");
            return true;
        }
        let unary = match value {
            Int64From32(inner) => Some((inner, "Int64From32")),
            UInt64From32(inner) => Some((inner, "UInt64From32")),
            UInt32From64(inner) => Some((inner, "UInt32From64")),
            Int64FromUInt32(inner) => Some((inner, "Int64FromUInt32")),
            UInt64FromInt32(inner) => Some((inner, "UInt64FromInt32")),
            UInt64FromInt64(inner) => Some((inner, "UInt64FromInt64")),
            BitwiseNot(inner) => Some((inner, "BitwiseNot")),
            Int64BitwiseNot(inner) => Some((inner, "Int64BitwiseNot")),
            UInt64BitwiseNot(inner) => Some((inner, "UInt64BitwiseNot")),
            _ => None,
        };
        if let Some((inner, name)) = unary {
            self.push(name);
            self.push("(");
            self.bitvector(inner);
            self.push(")");
            return true;
        }
        if let If {
            condition,
            then_term,
            else_term,
        } = value
        {
            self.push("if(");
            self.condition(condition);
            self.push(", ");
            self.bitvector(then_term);
            self.push(", ");
            self.bitvector(else_term);
            self.push(")");
            return true;
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{AlgebraicType, CMemoryRange, CValue, LoadKind, ResourceContext};

    fn render(fact: &Proposition) -> String {
        render_trace_fact_labeled(fact, &mut SnapshotLabels::default())
    }

    #[test]
    fn inventory_fact_kinds_show_operands_instead_of_opaque_counts() {
        let p = Pointer::symbolic(Variable(986_700));
        let memory = CMemory::new();
        let word = Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory_ref(&memory),
            Box::new(p.clone()),
            LoadKind::Bits64,
        );
        let field = CResource::Memory(CMemoryRange::new_with_element_width(
            p.clone(),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
            8,
        ));
        let composite = CResource::Composite {
            name: "rb_child_links".into(),
            arguments: std::sync::Arc::from([AlgebraicValue::C(CValue::Int32(
                Bitvector32Term::Constant(7),
            ))]),
        };
        let model = AlgebraicTerm {
            algebraic_type: AlgebraicType::parameter("Tree".into()),
            node: AlgebraicTermNode::Variable(Variable(986_701)),
        };
        let context = ResourceContext::new().unchecked_with_fact(CResourceFact::Own(
            field.clone(),
            Box::new(Bitvector32Term::Constant(1)),
        ));
        let facts = [
            (
                Proposition::ConditionIs(
                    ConditionTerm::Bitvector64Equal(
                        Box::new(Bitvector32Term::UInt64BitwiseAnd(
                            Box::new(word),
                            Box::new(Bitvector32Term::UInt64Constant(1)),
                        )),
                        Box::new(Bitvector32Term::UInt64Constant(0)),
                    ),
                    true,
                ),
                "read<Bits64>",
            ),
            (
                Proposition::ConditionIs(
                    ConditionTerm::Bitvector32Equal(
                        Box::new(Bitvector32Term::ClickFunctionApplication {
                            name: "rb_root_black".into(),
                            arguments: vec![PureFunctionArgument::Algebraic(model.clone())],
                        }),
                        Box::new(Bitvector32Term::Constant(1)),
                    ),
                    true,
                ),
                "rb_root_black(",
            ),
            (
                Proposition::ConditionIs(
                    ConditionTerm::PointerEqual(Box::new(p.clone()), Box::new(Pointer::null())),
                    false,
                ),
                "is false",
            ),
            (
                Proposition::Equal(Term::Algebraic(model.clone()), Term::Algebraic(model)),
                ":Tree",
            ),
            (
                Proposition::ConditionIs(
                    ConditionTerm::PointerOffsetEqual(
                        Box::new(p.offset.clone()),
                        Box::new(PointerOffsetTerm::Constant(16)),
                    ),
                    true,
                ),
                "16",
            ),
            (
                Proposition::CMemoryLoadable {
                    memory,
                    base: p,
                    bytes: Bitvector32Term::Constant(8),
                    wide: false,
                },
                "bytes:uint32=8",
            ),
            (Proposition::CResourceComposition(context), "owns memory("),
            (
                Proposition::CResourceContains {
                    parent: Box::new(composite),
                    child: Box::new(field),
                },
                "rb_child_links(int32(7)) contains",
            ),
            (
                Proposition::Predicate {
                    name: "__click_volatile_write_123".into(),
                    arguments: vec![Term::CValue(CValue::UInt64(
                        Bitvector32Term::UInt64Constant(1),
                    ))],
                },
                "volatile-write-event#123(uint64(1u64))",
            ),
        ];
        for (fact, expected) in facts {
            let text = render(&fact);
            assert!(text.contains(expected), "{text}");
            assert!(
                !text.contains("opaque")
                    && !text.contains("bounded operation")
                    && !text.contains("no exact"),
                "{text}"
            );
        }
    }

    #[test]
    fn trace_reads_preserve_snapshot_and_load_kind_without_current_pointer_names() {
        let address = Pointer::symbolic(Variable(986_702));
        let first = crate::kernel::intern_c_memory(CMemory::new());
        let second = crate::kernel::intern_c_memory(CMemory::new().with_block("trace_changed", 4));
        let load = |memory, kind| {
            Term::Bitvector32(Bitvector32Term::MemoryLoad(
                memory,
                Box::new(address.clone()),
                kind,
            ))
        };
        let fact = Proposition::Equal(load(first, LoadKind::UInt8), load(second, LoadKind::Bits64));
        let mut labels = SnapshotLabels::default();
        labels.source_name(Variable(986_702), "mutable_local".into());
        let text = render_trace_fact_labeled(&fact, &mut labels);
        assert!(
            text.contains("read<UInt8>(snapshot#1, pointer=value#1)"),
            "{text}"
        );
        assert!(
            text.contains("read<Bits64>(snapshot#2, pointer=value#1)"),
            "{text}"
        );
        assert!(!text.contains("mutable_local"));
    }

    #[test]
    fn resource_composition_lists_bounded_entries_and_explicit_omissions() {
        for count in [8, 64, 512] {
            let context = ResourceContext::new().unchecked_with_facts((0..count).map(|id| {
                CResourceFact::View(CResource::Token {
                    name: format!("token_{id}"),
                    arguments: std::sync::Arc::from([]),
                })
            }));
            let text = render(&Proposition::CResourceComposition(context));
            assert_eq!(text.matches("views token_").count(), 8, "{text}");
            assert_eq!(text.contains("more entries"), count > 8, "{text}");
            assert!(text.contains("support details omitted"));
            assert!(text.len() < 1024);
        }
    }

    #[test]
    fn machine_operations_keep_width_signedness_and_casts() {
        let a = Box::new(Bitvector32Term::Variable(Variable(986_703)));
        let b = Box::new(Bitvector32Term::Constant(2));
        for (value, expected) in [
            (Bitvector32Term::Int64Divide(a.clone(), b.clone()), "int64("),
            (
                Bitvector32Term::UInt64Divide(a.clone(), b.clone()),
                "uint64(",
            ),
            (
                Bitvector32Term::LogicalShiftRight(a.clone(), b.clone()),
                "lshr",
            ),
            (Bitvector32Term::ArithmeticShiftRight(a.clone(), b), "ashr"),
            (Bitvector32Term::UInt64FromInt32(a), "UInt64FromInt32("),
        ] {
            let text = render(&Proposition::Equal(
                Term::Bitvector32(value),
                Term::Bitvector32(Bitvector32Term::Constant(0)),
            ));
            assert!(text.contains(expected), "{text}");
        }
    }
}

#[cfg(test)]
mod extended_snapshot_tests {
    use super::*;

    #[test]
    fn trace_labels_retain_late_snapshot_identities_without_more_structural_comparisons() {
        let mut labels = SnapshotLabels::default();
        let fact = Proposition::ConditionIs(ConditionTerm::Constant(true), true);
        render_trace_fact_labeled(&fact, &mut labels);
        let memories: Vec<_> = (0..64)
            .map(|i| CMemory::new().with_block(format!("late_{i}"), 8))
            .collect();
        for (i, memory) in memories.iter().enumerate() {
            assert_eq!(labels.snapshot_name(memory), format!("snapshot#{}", i + 1));
        }
        for (i, memory) in memories.iter().enumerate().rev() {
            assert_eq!(
                labels.snapshot_name(&memory.clone()),
                format!("snapshot#{}", i + 1)
            );
        }
        assert!(
            labels
                .trace_legend()
                .contains("separately constructed equal memories")
        );
    }
}
