//! Expression results retain produced machine DAGs across deferred evaluation.
//! Native inputs and unmigrated sorts cross an explicit compatibility boundary;
//! there is no implicit dereference or cached parallel expression tree.
use super::*;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::kernel) enum SpecValue {
    Native(CValue),
    Shared(KernelTerm),
}

impl From<CValue> for SpecValue {
    fn from(value: CValue) -> Self {
        Self::Native(value)
    }
}
impl From<KernelTerm> for SpecValue {
    fn from(value: KernelTerm) -> Self {
        Self::Shared(value)
    }
}
impl SpecValue {
    pub(in crate::kernel) fn into_native(self) -> CValue {
        match self {
            Self::Native(value) => value,
            Self::Shared(term) => {
                let PureFunctionArgument::Value(value) = KernelTermExport::default()
                    .argument(&term)
                    .expect("machine expression result")
                else {
                    unreachable!()
                };
                value
            }
        }
    }
    pub(in crate::kernel) fn native(&self) -> std::borrow::Cow<'_, CValue> {
        match self {
            Self::Native(value) => std::borrow::Cow::Borrowed(value),
            Self::Shared(_) => std::borrow::Cow::Owned(self.clone().into_native()),
        }
    }
    pub(in crate::kernel) fn c_type(&self) -> CType {
        match self {
            Self::Native(value) => value.c_type(),
            Self::Shared(term) => match term.ty() {
                KernelType::C(ty) => *ty,
                _ => unreachable!(),
            },
        }
    }
    pub(super) fn numeric(self) -> Self {
        match self {
            Self::Native(value) => Self::Native(value.numeric_value().clone()),
            shared => shared,
        }
    }
    pub(super) fn machine(&self) -> Option<(MachineIntegerType, MachineOperandView<'_>)> {
        let format = MachineIntegerType::from_c_type(self.c_type())?;
        match self {
            Self::Native(value) => {
                let (crate::kernel::integer_c_value!(term)) = value else {
                    return None;
                };
                Some((format, MachineOperandView::Legacy(term)))
            }
            Self::Shared(term) => Some((format, MachineOperandView::Shared(term))),
        }
    }
    pub(super) fn observe(&self) -> Option<IntegerTerm> {
        // Opaque leaves have producer-specific identities; their observation
        // consumers still use native identity. Read the retained summary,
        // without traversing a growing arithmetic prefix to select this boundary.
        if let Self::Shared(root) = self
            && !root.has_opaque_observation_boundary()
        {
            let (format, view) = self.machine()?;
            return view.observe(format);
        }
        let value = self.native();
        IntegerTerm::from_machine(
            MachineIntegerType::from_c_type(value.c_type())?,
            c_value_bitvector_term(&value)?,
        )
    }
    pub(super) fn comparison(
        &self,
        op: CComparisonOperator,
        right: &Self,
    ) -> ExecutionResult<Option<Proposition>> {
        // Proposition consumers still distinguish native machine comparisons
        // from Integer observations (including pointer-word proof routing).
        // Keep this explicit boundary until those consumers share a view.
        let left = self.native();
        let right = right.native();
        Ok(bool_comparison_proposition(&left, op, &right)
            .transpose()?
            .or_else(|| c_value_comparison_proposition(&left, op, &right)))
    }
}
