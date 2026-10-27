//! Authority to enumerate ambient facts while planning an expandable proof.

/// Checking may accept this capability, but only planning can construct it.
/// It authorizes search enumeration, not a proof conclusion or a cost bound.
pub(crate) struct SearchPermission {
    _private: (),
}

impl SearchPermission {
    pub(super) const fn new() -> Self {
        Self { _private: () }
    }
}
