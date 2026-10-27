use super::{Proposition, PureFactContext};

/// A reasoning input containing only explicitly supplied premises. Ambient
/// contexts can enter this API only from a planner holding search permission.
/// The private field and absence of DerefMut prevent checking from upgrading
/// an ambient context or adding unselected facts.
pub(crate) struct SelectedFacts {
    context: PureFactContext,
}

impl SelectedFacts {
    pub(crate) fn from_propositions(propositions: &[Proposition]) -> Self {
        Self {
            context: propositions
                .iter()
                .fold(PureFactContext::new(), |context, premise| {
                    context
                        .assume_proposition(crate::kernel::clone_proposition_iteratively(premise))
                }),
        }
    }

    pub(crate) fn for_search(
        context: &PureFactContext,
        _permission: crate::SearchPermission,
    ) -> Self {
        Self {
            context: context.clone(),
        }
    }
}

impl std::ops::Deref for SelectedFacts {
    type Target = PureFactContext;
    fn deref(&self) -> &PureFactContext {
        &self.context
    }
}

#[cfg(test)]
impl PureFactContext {
    pub(crate) fn selected_for_test(&self) -> SelectedFacts {
        SelectedFacts {
            context: self.clone(),
        }
    }
}
