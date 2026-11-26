//! Exact read descriptions and the version identities used to compare them.
//!
//! `OldMachineTerm::memory_read` constructs the exact descriptor. Selecting a
//! comparison identity is a separate legacy operation: it may choose another
//! memory state, but never mutates the descriptor it receives. Observation
//! publication is separate from both. The parent module retains the existing
//! cache and compatibility policy until logical reads migrate to exact states.

use super::*;

/// A borrowed view of the exact memory, address, and kind written in a read.
/// Constructing this view performs no version selection or registry lookup.
#[derive(Clone, Copy)]
pub(super) struct ScalarReadDescriptor<'a> {
    term: &'a OldMachineTerm,
    point: &'a ProgramPoint,
    memory: &'a SharedMemory,
    pointer: &'a Address,
    kind: LoadKind,
    narrow_bytes: Option<u32>,
}

impl<'a> ScalarReadDescriptor<'a> {
    pub(super) fn memory(&self) -> &'a SharedMemory {
        self.memory
    }

    /// The read's own point, whose memory [`Self::memory`] is.
    pub(super) fn point(&self) -> &'a ProgramPoint {
        self.point
    }

    pub(super) fn address(&self) -> &'a Address {
        self.pointer
    }

    pub(super) fn narrow_bytes(&self) -> Option<u32> {
        self.narrow_bytes
    }

    pub(super) fn from_term(term: &'a OldMachineTerm) -> Option<Self> {
        let OldMachineTerm::MemoryLoad(memory, pointer, kind) = term else {
            return None;
        };
        Some(Self {
            term,
            point: memory,
            memory: memory.shared_memory(),
            pointer,
            kind: *kind,
            // A native byte/halfword keeps its width even when a wider
            // observation was recorded at this address.
            narrow_bytes: match kind {
                LoadKind::Int8 | LoadKind::UInt8 => Some(1),
                LoadKind::Int16 | LoadKind::UInt16 => Some(2),
                _ => None,
            },
        })
    }
}

/// A selected read's comparison identity, distinct from the exact descriptor.
///
/// This transparent wrapper preserves the existing cache representation. Its
/// term conversion is deliberately named as legacy policy: current callers
/// still retain selected version reads, rather than their original descriptors.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ScalarReadComparisonIdentity(OldMachineTerm);

impl ScalarReadComparisonIdentity {
    pub(super) fn as_legacy_read(&self) -> &OldMachineTerm {
        &self.0
    }

    pub(super) fn into_legacy_read(self) -> OldMachineTerm {
        self.0
    }
}

/// The existing cold version-selection route, with no new callers or walks.
/// This does not publish the selected read's observation; the compatibility
/// adapter does so once, after selection and before filling its cache.
/// `observed_bytes` distinguishes a known access width from the conservative
/// untyped default, preserving the adapter's cache invalidation rules.
pub(super) fn select_comparison_identity(
    read: ScalarReadDescriptor<'_>,
) -> (ScalarReadComparisonIdentity, Option<u32>) {
    let ScalarReadDescriptor {
        term: bits,
        point: _,
        memory: origin,
        pointer: original_pointer,
        kind: original_kind,
        narrow_bytes,
    } = read;
    let canonical = crate::kernel::memory_history::canonicalize_atomic_loads(bits);
    let candidate = match &canonical {
        OldMachineTerm::Variable(variable) => registered_load_term_for_variable(variable)
            .filter(
                |read| matches!(read, OldMachineTerm::MemoryLoad(_, address, kind) if address.as_ref() == original_pointer && *kind == original_kind),
            )
            .unwrap_or_else(|| bits.clone()),
        OldMachineTerm::MemoryLoad(memory, pointer, kind) if pointer.as_ref() == original_pointer && *kind == original_kind => {
            let held = memory
                .memory()
                .known_value(pointer)
                .and_then(|value| crate::kernel::spec::program_value_bitvector_term(&value))
                .and_then(|held| match held {
                    OldMachineTerm::Variable(variable) => registered_load_term_for_variable(&variable),
                    read @ OldMachineTerm::MemoryLoad(..) => Some(read),
                    _ => None,
                })
                .filter(|held| {
                    matches!(held, OldMachineTerm::MemoryLoad(_, at, held_kind)
                    if at.address() == pointer.address() && held_kind == kind)
                });
            held.unwrap_or(canonical)
        }
        _ => bits.clone(),
    };
    let OldMachineTerm::MemoryLoad(memory, pointer, kind) = candidate else {
        unreachable!("selected scalar read")
    };
    let recorded_bytes = narrow_bytes
        .or_else(|| recorded_load_access_width(origin, original_pointer))
        .or_else(|| recorded_load_access_width(memory.shared_memory(), &pointer))
        .or_else(|| {
            existing_read_access_width(origin, original_pointer, original_kind).max(
                existing_read_access_width(memory.shared_memory(), &pointer, kind),
            )
        });
    let bytes = recorded_bytes.unwrap_or_else(|| kind.unrecorded_access_byte_width());
    let version = crate::kernel::resource_tracker::last_same_version_point(
        crate::kernel::resource_tracker::TrackedResource::Cell {
            pointer: &pointer,
            bytes: bytes.into(),
        },
        &memory,
    )
    .unwrap_or_else(|| memory.into());
    (
        ScalarReadComparisonIdentity(OldMachineTerm::read_named(version, pointer, kind)),
        recorded_bytes,
    )
}

/// Publish width, defining state, and live origin for a selected identity.
/// This is bookkeeping, not the construction or selection of the read term.
pub(super) fn record_comparison_observation(
    identity: &ScalarReadComparisonIdentity,
    origin: &ProgramPoint,
    observed_bytes: Option<u32>,
) {
    let OldMachineTerm::MemoryLoad(memory, pointer, kind) = identity.as_legacy_read() else {
        unreachable!("selected scalar read identity");
    };
    // The identity is memory-named; place it where the read's own point is.
    let point = ProgramPoint::viewing(memory.shared_memory(), memory);
    let origin = ProgramPoint::viewing(origin.shared_memory(), origin);
    let id = match observed_bytes {
        Some(bytes) => read_observations::record_at(&point, pointer, *kind, &origin, bytes),
        None => read_observations::record_untyped_at(&point, pointer, *kind, &origin),
    };
    read_observations::select(id);
}
