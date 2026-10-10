//! Explicit C thread-runtime assumptions. The modeled binding is a conditional
//! client-verification profile; no native pthread implementation is certified.

use sha2::{Digest, Sha256};

/// The resource interface planned for the four selected pthread mutex calls.
/// This describes contract binders; it does not implement a `CFunction`
/// contract or authorize any resource transfer in the verifier.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum MutexOperation {
    Init,
    Lock,
    Unlock,
    Destroy,
}

impl MutexOperation {
    pub const ALL: [Self; 4] = [Self::Init, Self::Lock, Self::Unlock, Self::Destroy];

    pub fn for_function_name(name: &str) -> Option<Self> {
        Self::ALL
            .into_iter()
            .find(|operation| operation.descriptor().function_name == name)
    }

    pub const fn descriptor(self) -> &'static MutexContractDescriptor {
        match self {
            Self::Init => &MUTEX_INIT_CONTRACT,
            Self::Lock => &MUTEX_LOCK_CONTRACT,
            Self::Unlock => &MUTEX_UNLOCK_CONTRACT,
            Self::Destroy => &MUTEX_DESTROY_CONTRACT,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum MutexResourceRole {
    Storage,
    Lifetime,
    Access,
    Guard,
    State,
}

impl MutexResourceRole {
    pub const fn name(self) -> &'static str {
        match self {
            Self::Storage => "storage",
            Self::Lifetime => "lifetime",
            Self::Access => "access",
            Self::Guard => "guard",
            Self::State => "state",
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum MutexBinderMode {
    Own,
    Consume,
    Produce,
}

/// Stable identities for contract-local binders. The init state identity
/// preserves the binder already used by the current publication transport.
pub const MUTEX_INIT_STORAGE_BINDER_ID: u64 = u64::MAX - 2;
pub const MUTEX_INIT_STATE_BINDER_ID: u64 = u64::MAX - 1;
pub const MUTEX_INIT_LIFETIME_BINDER_ID: u64 = u64::MAX - 3;
pub const MUTEX_LOCK_ACCESS_BINDER_ID: u64 = u64::MAX - 4;
pub const MUTEX_LOCK_GUARD_BINDER_ID: u64 = u64::MAX - 5;
pub const MUTEX_LOCK_STATE_BINDER_ID: u64 = u64::MAX - 6;
pub const MUTEX_UNLOCK_ACCESS_BINDER_ID: u64 = u64::MAX - 7;
pub const MUTEX_UNLOCK_GUARD_BINDER_ID: u64 = u64::MAX - 8;
pub const MUTEX_UNLOCK_STATE_BINDER_ID: u64 = u64::MAX - 9;
pub const MUTEX_DESTROY_LIFETIME_BINDER_ID: u64 = u64::MAX - 10;
pub const MUTEX_DESTROY_STORAGE_BINDER_ID: u64 = u64::MAX - 11;
pub const MUTEX_DESTROY_STATE_BINDER_ID: u64 = u64::MAX - 12;
/// The resource type an `atomic_init` call publishes through its flag.
pub const ATOMIC_INIT_PAYLOAD_BINDER_ID: u64 = u64::MAX - 13;

/// The C11 atomic operations of the one-shot publication subset.
pub const ATOMIC_INIT_NAME: &str = "atomic_init";
pub const ATOMIC_STORE_NAME: &str = "atomic_store_explicit";
pub const ATOMIC_LOAD_NAME: &str = "atomic_load_explicit";

pub fn is_publication_operation(name: &str) -> bool {
    matches!(
        name,
        ATOMIC_INIT_NAME | ATOMIC_STORE_NAME | ATOMIC_LOAD_NAME
    )
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct MutexResourceBinder {
    pub identity: u64,
    pub role: MutexResourceRole,
    pub mode: MutexBinderMode,
    /// Only implemented binders may participate in current named transport.
    /// Other entries describe the planned contract without enabling it.
    pub implemented: bool,
}

impl MutexResourceBinder {
    pub const fn name(self) -> &'static str {
        self.role.name()
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct MutexContractDescriptor {
    pub function_name: &'static str,
    pub arity: usize,
    pub binders: &'static [MutexResourceBinder],
}

impl MutexContractDescriptor {
    pub fn binder_by_name(&self, name: &str) -> Option<&MutexResourceBinder> {
        self.binders.iter().find(|binder| binder.name() == name)
    }

    pub fn binder_by_id(&self, identity: u64) -> Option<&MutexResourceBinder> {
        self.binders
            .iter()
            .find(|binder| binder.identity == identity)
    }

    pub fn binder_by_role(&self, role: MutexResourceRole) -> Option<&MutexResourceBinder> {
        self.binders.iter().find(|binder| binder.role == role)
    }

    /// The staged projection accepted by ordinary named-binder validation.
    /// Currently initialization's consumed `state` and produced `lifetime`,
    /// and destruction's consumed `lifetime`, are implemented.
    pub fn implemented_binders(&self) -> impl Iterator<Item = &MutexResourceBinder> {
        self.binders.iter().filter(|binder| binder.implemented)
    }

    pub fn implemented_binder_by_name(&self, name: &str) -> Option<&MutexResourceBinder> {
        self.binder_by_name(name)
            .filter(|binder| binder.implemented)
    }
}

const INIT_BINDERS: [MutexResourceBinder; 3] = [
    MutexResourceBinder {
        identity: MUTEX_INIT_STORAGE_BINDER_ID,
        role: MutexResourceRole::Storage,
        mode: MutexBinderMode::Consume,
        implemented: false,
    },
    MutexResourceBinder {
        identity: MUTEX_INIT_STATE_BINDER_ID,
        role: MutexResourceRole::State,
        mode: MutexBinderMode::Consume,
        implemented: true,
    },
    MutexResourceBinder {
        identity: MUTEX_INIT_LIFETIME_BINDER_ID,
        role: MutexResourceRole::Lifetime,
        mode: MutexBinderMode::Produce,
        implemented: true,
    },
];

const LOCK_BINDERS: [MutexResourceBinder; 3] = [
    MutexResourceBinder {
        identity: MUTEX_LOCK_ACCESS_BINDER_ID,
        role: MutexResourceRole::Access,
        mode: MutexBinderMode::Own,
        implemented: true,
    },
    MutexResourceBinder {
        identity: MUTEX_LOCK_GUARD_BINDER_ID,
        role: MutexResourceRole::Guard,
        mode: MutexBinderMode::Produce,
        implemented: true,
    },
    MutexResourceBinder {
        identity: MUTEX_LOCK_STATE_BINDER_ID,
        role: MutexResourceRole::State,
        mode: MutexBinderMode::Produce,
        implemented: true,
    },
];

const UNLOCK_BINDERS: [MutexResourceBinder; 3] = [
    MutexResourceBinder {
        identity: MUTEX_UNLOCK_ACCESS_BINDER_ID,
        role: MutexResourceRole::Access,
        mode: MutexBinderMode::Own,
        implemented: true,
    },
    MutexResourceBinder {
        identity: MUTEX_UNLOCK_GUARD_BINDER_ID,
        role: MutexResourceRole::Guard,
        mode: MutexBinderMode::Consume,
        implemented: true,
    },
    MutexResourceBinder {
        identity: MUTEX_UNLOCK_STATE_BINDER_ID,
        role: MutexResourceRole::State,
        mode: MutexBinderMode::Consume,
        implemented: true,
    },
];

const DESTROY_BINDERS: [MutexResourceBinder; 3] = [
    MutexResourceBinder {
        identity: MUTEX_DESTROY_LIFETIME_BINDER_ID,
        role: MutexResourceRole::Lifetime,
        mode: MutexBinderMode::Consume,
        implemented: true,
    },
    MutexResourceBinder {
        identity: MUTEX_DESTROY_STORAGE_BINDER_ID,
        role: MutexResourceRole::Storage,
        mode: MutexBinderMode::Produce,
        implemented: false,
    },
    MutexResourceBinder {
        identity: MUTEX_DESTROY_STATE_BINDER_ID,
        role: MutexResourceRole::State,
        mode: MutexBinderMode::Produce,
        implemented: false,
    },
];

pub const MUTEX_INIT_CONTRACT: MutexContractDescriptor = MutexContractDescriptor {
    function_name: "pthread_mutex_init",
    arity: 2,
    binders: &INIT_BINDERS,
};
pub const MUTEX_LOCK_CONTRACT: MutexContractDescriptor = MutexContractDescriptor {
    function_name: "pthread_mutex_lock",
    arity: 1,
    binders: &LOCK_BINDERS,
};
pub const MUTEX_UNLOCK_CONTRACT: MutexContractDescriptor = MutexContractDescriptor {
    function_name: "pthread_mutex_unlock",
    arity: 1,
    binders: &UNLOCK_BINDERS,
};
pub const MUTEX_DESTROY_CONTRACT: MutexContractDescriptor = MutexContractDescriptor {
    function_name: "pthread_mutex_destroy",
    arity: 1,
    binders: &DESTROY_BINDERS,
};

/// Retained identity of the selected pthread declarations and trusted
/// modeled specification. A verifier attaches this only after checking
/// declaration provenance and call shapes.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ModeledPthreadBinding {
    pub target: super::target::CTarget,
    pub specification_version: u32,
    pub header_digest: [u8; 32],
    /// Click's `<stdatomic.h>` projection, which declares the modeled
    /// publication operations.
    pub atomic_header_digest: [u8; 32],
    pub specification_digest: [u8; 32],
    pub create_name: &'static str,
    pub join_name: &'static str,
    pub mutex_init_name: &'static str,
    pub mutex_lock_name: &'static str,
    pub mutex_unlock_name: &'static str,
    /// Storage extent fixed by the selected modeled pthread ABI.
    pub mutex_storage_bytes: u32,
    pub mutex_storage_alignment: u32,
    pub mutex_destroy_name: &'static str,
    pub requires_null_attributes: bool,
    pub requires_direct_worker: bool,
    pub requires_null_join_result: bool,
}

impl ModeledPthreadBinding {
    pub fn builtin() -> Self {
        Self {
            target: super::target::CTarget::X86_64LinuxUserspace,
            specification_version: 11,
            header_digest: Sha256::digest(include_str!("modeled_pthread.h").as_bytes()).into(),
            atomic_header_digest: Sha256::digest(include_str!("modeled_stdatomic.h").as_bytes())
                .into(),
            specification_digest: Sha256::digest(
                include_str!("modeled_pthread_spec.md").as_bytes(),
            )
            .into(),
            create_name: "pthread_create",
            join_name: "pthread_join",
            mutex_init_name: "pthread_mutex_init",
            mutex_lock_name: "pthread_mutex_lock",
            mutex_unlock_name: "pthread_mutex_unlock",
            mutex_storage_bytes: 40,
            mutex_storage_alignment: 8,
            mutex_destroy_name: "pthread_mutex_destroy",
            requires_null_attributes: true,
            requires_direct_worker: true,
            requires_null_join_result: true,
        }
    }

    pub fn identity(&self) -> String {
        let mut hasher = Sha256::new();
        for part in [
            b"click-modeled-pthread-binding-v2".as_slice(),
            self.target.name().as_bytes(),
            &self.specification_version.to_be_bytes(),
            &self.header_digest,
            &self.atomic_header_digest,
            &self.specification_digest,
            self.create_name.as_bytes(),
            self.join_name.as_bytes(),
            self.mutex_init_name.as_bytes(),
            self.mutex_lock_name.as_bytes(),
            self.mutex_unlock_name.as_bytes(),
            self.mutex_destroy_name.as_bytes(),
            &self.mutex_storage_bytes.to_be_bytes(),
            &self.mutex_storage_alignment.to_be_bytes(),
            &[
                self.requires_null_attributes as u8,
                self.requires_direct_worker as u8,
                self.requires_null_join_result as u8,
            ],
        ] {
            hasher.update((part.len() as u64).to_be_bytes());
            hasher.update(part);
        }
        format!("modeled-pthread:{:x}", hasher.finalize())
    }
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum CThreadRuntime {
    #[default]
    None,
    ModeledPthread,
}

impl CThreadRuntime {
    pub fn from_name(name: &str) -> Option<Self> {
        match name {
            "modeled-pthread" => Some(Self::ModeledPthread),
            _ => None,
        }
    }

    pub const fn name(self) -> Option<&'static str> {
        match self {
            Self::None => None,
            Self::ModeledPthread => Some("modeled-pthread"),
        }
    }

    /// Participates in both proof and incremental-session identities. The
    /// actual built-in declarations and specification bytes invalidate a
    /// cached modeled proof when either changes.
    pub fn identity_suffix(self) -> Option<String> {
        match self {
            Self::None => None,
            Self::ModeledPthread => Some(ModeledPthreadBinding::builtin().identity()),
        }
    }

    pub const fn assumption(self) -> Option<&'static str> {
        match self {
            Self::None => None,
            Self::ModeledPthread => Some(
                "modeled-pthread v11: pthread create/join, shared mutex calls, and one-shot atomic publication obey the trusted Click specification; native runtime binding unvalidated",
            ),
        }
    }
}

#[cfg(test)]
mod assumption_tests {
    use super::*;

    #[test]
    fn the_runtime_assumption_names_the_builtin_specification_version() {
        let version = ModeledPthreadBinding::builtin().specification_version;
        let assumption = CThreadRuntime::ModeledPthread
            .assumption()
            .expect("the modeled runtime states its assumption");
        assert!(
            assumption.starts_with(&format!("modeled-pthread v{version}:")),
            "{assumption}"
        );
    }
}

#[cfg(test)]
mod mutex_contract_tests {
    use super::{MutexBinderMode as Mode, MutexOperation as Op, MutexResourceRole as Role, *};
    use std::collections::BTreeSet;

    #[test]
    fn planned_contracts_have_stable_distinct_binders() {
        let expected: [(Op, &str, usize, &[(Role, Mode, u64)]); 4] = [
            (
                Op::Init,
                "pthread_mutex_init",
                2,
                &[
                    (Role::Storage, Mode::Consume, u64::MAX - 2),
                    (Role::State, Mode::Consume, MUTEX_INIT_STATE_BINDER_ID),
                    (Role::Lifetime, Mode::Produce, u64::MAX - 3),
                ],
            ),
            (
                Op::Lock,
                "pthread_mutex_lock",
                1,
                &[
                    (Role::Access, Mode::Own, u64::MAX - 4),
                    (Role::Guard, Mode::Produce, u64::MAX - 5),
                    (Role::State, Mode::Produce, u64::MAX - 6),
                ],
            ),
            (
                Op::Unlock,
                "pthread_mutex_unlock",
                1,
                &[
                    (Role::Access, Mode::Own, u64::MAX - 7),
                    (Role::Guard, Mode::Consume, u64::MAX - 8),
                    (Role::State, Mode::Consume, u64::MAX - 9),
                ],
            ),
            (
                Op::Destroy,
                "pthread_mutex_destroy",
                1,
                &[
                    (Role::Lifetime, Mode::Consume, u64::MAX - 10),
                    (Role::Storage, Mode::Produce, u64::MAX - 11),
                    (Role::State, Mode::Produce, u64::MAX - 12),
                ],
            ),
        ];
        let mut identities = BTreeSet::new();
        for (operation, function_name, arity, binders) in expected {
            let descriptor = operation.descriptor();
            assert_eq!(Op::for_function_name(function_name), Some(operation));
            assert_eq!(descriptor.function_name, function_name);
            assert_eq!(descriptor.arity, arity);
            assert_eq!(descriptor.binders.len(), binders.len());
            for &(role, mode, identity) in binders {
                let binder = descriptor.binder_by_role(role).unwrap();
                assert_eq!(
                    (binder.role, binder.mode, binder.identity),
                    (role, mode, identity)
                );
                assert_eq!(descriptor.binder_by_name(role.name()), Some(binder));
                assert_eq!(descriptor.binder_by_id(identity), Some(binder));
                assert!(identities.insert(identity));
            }
        }
        assert_eq!(Op::for_function_name("pthread_create"), None);
    }

    #[test]
    fn staged_named_transport_exposes_supported_lifecycle_and_use_binders() {
        for operation in Op::ALL {
            let descriptor = operation.descriptor();
            let implemented = descriptor
                .implemented_binders()
                .map(|binder| (binder.role, binder.mode, binder.identity))
                .collect::<Vec<_>>();
            let expected = match operation {
                Op::Init => vec![
                    (Role::State, Mode::Consume, MUTEX_INIT_STATE_BINDER_ID),
                    (Role::Lifetime, Mode::Produce, MUTEX_INIT_LIFETIME_BINDER_ID),
                ],
                Op::Destroy => vec![(
                    Role::Lifetime,
                    Mode::Consume,
                    MUTEX_DESTROY_LIFETIME_BINDER_ID,
                )],
                Op::Lock => vec![
                    (Role::Access, Mode::Own, MUTEX_LOCK_ACCESS_BINDER_ID),
                    (Role::Guard, Mode::Produce, MUTEX_LOCK_GUARD_BINDER_ID),
                    (Role::State, Mode::Produce, MUTEX_LOCK_STATE_BINDER_ID),
                ],
                Op::Unlock => vec![
                    (Role::Access, Mode::Own, MUTEX_UNLOCK_ACCESS_BINDER_ID),
                    (Role::Guard, Mode::Consume, MUTEX_UNLOCK_GUARD_BINDER_ID),
                    (Role::State, Mode::Consume, MUTEX_UNLOCK_STATE_BINDER_ID),
                ],
            };
            assert_eq!(implemented, expected);
            for binder in descriptor.binders {
                assert_eq!(
                    descriptor.implemented_binder_by_name(binder.name()),
                    binder.implemented.then_some(binder)
                );
            }
        }
    }
}
