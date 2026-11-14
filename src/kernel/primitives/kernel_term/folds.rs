//! Typed fold payloads, prepared before activating common fold roots.
//! Bounds and initial value are outside the two binders; only the body is in
//! their scope. Construction reads no facts and performs no fold reduction.
use super::*;

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub(crate) enum KernelFoldIndex {
    Int32,
    UInt64,
    Integer,
}

impl KernelFoldIndex {
    pub(crate) fn ty(self) -> KernelType {
        match self {
            Self::Int32 => KernelType::C(MachineIntegerType::Int32.c_type()),
            Self::UInt64 => KernelType::C(MachineIntegerType::UInt64.c_type()),
            Self::Integer => KernelType::Integer,
        }
    }
}

/// A shallow payload: expression children are common handles, not native
/// expression trees. Exact binder identities remain distinct from alpha keys.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub(crate) struct KernelFold {
    pub(crate) index: KernelFoldIndex,
    pub(crate) accumulator: Variable,
    pub(crate) item: Variable,
    /// Start, end, initial value, body, in that order.
    pub(crate) arguments: [KernelTerm; 4],
}

impl KernelFold {
    pub(crate) fn new(
        index: KernelFoldIndex,
        accumulator: Variable,
        item: Variable,
        arguments: [KernelTerm; 4],
    ) -> Result<Self, &'static str> {
        crate::instrumentation::record_deterministic_work(1);
        if arguments[0].ty() != &index.ty() || arguments[1].ty() != &index.ty() {
            return Err("fold bounds have the wrong index type");
        }
        if arguments[2].ty() != arguments[3].ty() {
            return Err("fold initial value and body have different types");
        }
        if arguments[2].ty() != &KernelType::Integer
            && !(index == KernelFoldIndex::Int32
                && arguments[2].ty() == &KernelType::C(CType::Int32))
        {
            return Err("unsupported fold result type");
        }
        Ok(Self {
            index,
            accumulator,
            item,
            arguments,
        })
    }

    pub(crate) fn result_type(&self) -> &KernelType {
        self.arguments[2].ty()
    }

    fn import_endpoint(
        import: &mut KernelTermImport,
        format: MachineIntegerType,
        endpoint: &SharedIntegerRangeEndpoint,
    ) -> KernelTerm {
        match endpoint.machine_operand().shared_operand() {
            Some(root) => root.with_machine_observation_type(format),
            None => import.machine(format, endpoint.value()),
        }
    }

    pub(crate) fn import_integer(
        import: &mut KernelTermImport,
        source: &IntegerTerm,
    ) -> Option<Self> {
        let IntegerTerm::RangeFold {
            index,
            initial,
            accumulator,
            item,
            body,
        } = source
        else {
            return None;
        };
        let (index, start, end) = match index {
            IntegerRangeFoldIndex::Int32 { start, end } => (
                KernelFoldIndex::Int32,
                Self::import_endpoint(import, MachineIntegerType::Int32, start),
                Self::import_endpoint(import, MachineIntegerType::Int32, end),
            ),
            IntegerRangeFoldIndex::UInt64 { start, end } => (
                KernelFoldIndex::UInt64,
                Self::import_endpoint(import, MachineIntegerType::UInt64, start),
                Self::import_endpoint(import, MachineIntegerType::UInt64, end),
            ),
            IntegerRangeFoldIndex::Integer { start, end } => (
                KernelFoldIndex::Integer,
                import.integer(start),
                import.integer(end),
            ),
        };
        Some(
            Self::new(
                index,
                *accumulator,
                *item,
                [start, end, import.integer(initial), import.integer(body)],
            )
            .expect("native Integer fold types"),
        )
    }

    pub(crate) fn import_machine(
        import: &mut KernelTermImport,
        source: &MachineTerm,
    ) -> Option<Self> {
        let MachineTerm::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } = source
        else {
            return None;
        };
        let mut read = |term| import.machine(MachineIntegerType::Int32, term);
        Some(
            Self::new(
                KernelFoldIndex::Int32,
                *accumulator,
                *item,
                [read(start), read(end), read(initial), read(body)],
            )
            .expect("native machine fold types"),
        )
    }

    pub(crate) fn export_integer(
        &self,
        export: &mut KernelTermExport,
    ) -> Result<IntegerTerm, &'static str> {
        if self.result_type() != &KernelType::Integer {
            return Err("expected Integer fold result");
        }
        let [start, end, initial, body] = &self.arguments;
        let index = match self.index {
            KernelFoldIndex::Int32 | KernelFoldIndex::UInt64 => {
                let start = SharedIntegerRangeEndpoint::intern(KernelTermExport::machine(start)?);
                let end = SharedIntegerRangeEndpoint::intern(KernelTermExport::machine(end)?);
                if self.index == KernelFoldIndex::Int32 {
                    IntegerRangeFoldIndex::Int32 { start, end }
                } else {
                    IntegerRangeFoldIndex::UInt64 { start, end }
                }
            }
            KernelFoldIndex::Integer => IntegerRangeFoldIndex::Integer {
                start: export.integer(start)?,
                end: export.integer(end)?,
            },
        };
        Ok(IntegerTerm::RangeFold {
            index,
            initial: export.integer(initial)?,
            accumulator: self.accumulator,
            item: self.item,
            body: export.integer(body)?,
        })
    }

    pub(crate) fn export_machine(&self) -> Result<MachineTerm, &'static str> {
        if self.result_type() != &KernelType::C(CType::Int32) {
            return Err("expected int32 fold result");
        }
        let [start, end, initial, body] = &self.arguments;
        Ok(MachineTerm::RangeFold {
            start: Box::new(KernelTermExport::machine(start)?),
            end: Box::new(KernelTermExport::machine(end)?),
            initial: Box::new(KernelTermExport::machine(initial)?),
            accumulator: self.accumulator,
            item: self.item,
            body: Box::new(KernelTermExport::machine(body)?),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fold_payload_roundtrips_preserve_ranges_binders_and_unreduced_bodies() {
        let start = SharedIntegerRangeEndpoint::intern(MachineTerm::Variable(Variable(10)));
        let end = SharedIntegerRangeEndpoint::intern(MachineTerm::constant(0));
        let indices = [
            IntegerRangeFoldIndex::Int32 {
                start: start.clone(),
                end: end.clone(),
            },
            IntegerRangeFoldIndex::UInt64 { start, end },
            IntegerRangeFoldIndex::Integer {
                start: IntegerTerm::Variable(Variable(10)).into(),
                end: IntegerTerm::constant_i64(-3).into(),
            },
        ];
        for index in indices {
            let native = IntegerTerm::RangeFold {
                index,
                initial: IntegerTerm::constant_i64(7).into(),
                accumulator: Variable(11),
                item: Variable(12),
                body: IntegerTerm::Add(
                    IntegerTerm::Variable(Variable(11)).into(),
                    IntegerTerm::constant_i64(0).into(),
                )
                .into(),
            };
            let common =
                KernelFold::import_integer(&mut KernelTermImport::default(), &native).unwrap();
            assert_eq!(
                common
                    .export_integer(&mut KernelTermExport::default())
                    .unwrap(),
                native
            );
            assert_eq!(common.result_type(), &KernelType::Integer);
            assert!(common.export_machine().is_err());
            let mut changed = common.clone();
            changed.item = Variable(13);
            assert_ne!(common, changed);
        }
        let native = MachineTerm::RangeFold {
            start: Box::new(MachineTerm::constant(9)),
            end: Box::new(MachineTerm::constant(2)),
            initial: Box::new(MachineTerm::constant(7)),
            accumulator: Variable(11),
            item: Variable(12),
            body: Box::new(MachineTerm::Variable(Variable(11))),
        };
        let common = KernelFold::import_machine(&mut KernelTermImport::default(), &native).unwrap();
        assert_eq!(common.export_machine().unwrap(), native);
        assert!(
            common
                .export_integer(&mut KernelTermExport::default())
                .is_err()
        );
    }

    #[test]
    fn fold_payload_rejects_mixed_bounds_results_and_unsupported_machine_sorts() {
        let int = KernelTerm::variable(KernelType::Integer, Variable(1));
        let machine = KernelTerm::variable(KernelType::C(CType::Int32), Variable(2));
        let wide = KernelTerm::variable(KernelType::C(CType::UInt64), Variable(3));
        for (index, args) in [
            (
                KernelFoldIndex::Integer,
                [int.clone(), machine.clone(), int.clone(), int.clone()],
            ),
            (
                KernelFoldIndex::Int32,
                [
                    machine.clone(),
                    machine.clone(),
                    machine.clone(),
                    int.clone(),
                ],
            ),
            (
                KernelFoldIndex::UInt64,
                [wide.clone(), wide.clone(), wide.clone(), wide],
            ),
        ] {
            assert!(KernelFold::new(index, Variable(4), Variable(5), args).is_err());
        }
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/kernel/primitives/kernel_term/folds.rs");
}
