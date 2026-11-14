//! Algebraic evaluator results. Symbolic matches retain their common roots;
//! consumers of the remaining native algebraic representation cross an
//! explicit compatibility boundary.
use super::*;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum AlgebraicResult {
    Native(AlgebraicTerm),
    Shared(KernelTerm),
}

impl From<AlgebraicTerm> for AlgebraicResult {
    fn from(value: AlgebraicTerm) -> Self {
        Self::Native(value)
    }
}

impl AlgebraicResult {
    pub(super) fn algebraic_type(&self) -> &AlgebraicType {
        match self {
            Self::Native(value) => &value.algebraic_type,
            Self::Shared(root) => {
                let KernelType::Algebraic(ty) = root.ty() else {
                    unreachable!("algebraic result type");
                };
                ty
            }
        }
    }

    pub(super) fn native_constructor(&self) -> Option<&AlgebraicTerm> {
        match self {
            Self::Native(value) if matches!(value.node, AlgebraicTermNode::Constructor { .. }) => {
                Some(value)
            }
            _ => None,
        }
    }

    pub(super) fn into_kernel(self) -> KernelTerm {
        match self {
            Self::Native(value) => {
                KernelTermImport::default().argument(&PureFunctionArgument::Algebraic(value))
            }
            Self::Shared(root) => root,
        }
    }

    pub(super) fn into_native_compat(self) -> AlgebraicTerm {
        match self {
            Self::Native(value) => value,
            Self::Shared(root) => KernelTermExport::default()
                .algebraic(&root)
                .expect("algebraic result compatibility boundary"),
        }
    }
}
