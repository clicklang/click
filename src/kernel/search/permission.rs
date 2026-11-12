//! Authority to enumerate ambient facts while planning an expandable proof.

/// Checking may accept this capability, but only planning can construct it.
/// It authorizes search enumeration, not a proof conclusion or a cost bound.
pub(crate) struct SearchPermission {
    _private: (),
}

impl SearchPermission {
    pub(super) fn new() -> Self {
        #[cfg(test)]
        super::record_discovery("SearchPermission::new");
        Self { _private: () }
    }
}
