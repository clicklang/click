// Scaling tests of `src/kernel/primitives/load.rs`: deterministic work
// measured at several input sizes. Included into its `scaling_tests` module;
// see "Scaling tests" in `docs/internals/testing.md`.

use super::*;
use crate::kernel::{
    CallbackSignature, ExecutionState, Pointer, ProgramType, ProgramValue, SymbolicMemory, Variable,
};

fn cell(index: u64) -> Address {
    Address {
        base: AddressBase::Concrete("local:load-cells".into()),
        offset: AddressOffset::Constant(8 * index as i64),
    }
}

/// Interning a load is one hash probe: the work to intern one more load,
/// and to find an interned one again, is the same however many loads of
/// other cells the session already holds (`design/loads.md`, open
/// question 3). Equality and hashing compare one number, so comparing two
/// loads of deeply nested cells costs no more than of flat ones.
#[test]
fn interning_a_load_is_flat_in_the_number_of_interned_loads() {
    let mut fresh = Vec::new();
    let mut found = Vec::new();
    for loads in [16u64, 256, 4096] {
        let _session = crate::kernel::VerificationSession::enter();
        let state = ExecutionState::new().begin_function_entry_memory();
        let point = state.program_point();
        let before = interned_load_count();
        for index in 0..loads {
            Load::at(point.clone(), &cell(index));
        }
        assert_eq!(interned_load_count() - before, loads as usize);
        let (next, work) = crate::instrumentation::measure_deterministic_work(|| {
            Load::at(point.clone(), &cell(loads))
        });
        fresh.push(work);
        let (again, work) = crate::instrumentation::measure_deterministic_work(|| {
            Load::at(point.clone(), &cell(loads))
        });
        assert_eq!(again, next);
        assert_eq!(interned_load_count() - before, loads as usize + 1);
        found.push(work);
    }
    assert!(fresh.iter().all(|&work| work == fresh[0]), "{fresh:?}");
    assert!(found.iter().all(|&work| work == found[0]), "{found:?}");
}

/// A load nested `depth` loads deep: the cell of each is the previous one.
fn nested_load(point: &ProgramPoint, depth: usize) -> Load {
    let mut load = Load::at(point.clone(), &cell(0));
    for _ in 0..depth {
        load = Load::at(point.clone(), &load.address());
    }
    load
}

/// Equality, hashing and ordering of loads read one interned id, whatever
/// the depth of the cell's address: comparing two loads of the same deep
/// cell is not a structural walk.
#[test]
fn comparing_loads_is_flat_in_cell_depth() {
    use std::hash::{Hash, Hasher};
    let _session = crate::kernel::VerificationSession::enter();
    let state = ExecutionState::new().begin_function_entry_memory();
    let point = state.program_point();
    let mut samples = Vec::new();
    for depth in [4, 64, 512] {
        let left = nested_load(&point, depth);
        let right = Load::at(point.clone(), left.cell());
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(left, right);
            assert_eq!(left.cmp(&right), std::cmp::Ordering::Equal);
            let hash = |load: &Load| {
                let mut state = std::collections::hash_map::DefaultHasher::new();
                load.hash(&mut state);
                state.finish()
            };
            assert_eq!(hash(&left), hash(&right));
        });
        samples.push(work);
    }
    assert!(
        samples.iter().all(|&work| work == samples[0]),
        "{samples:?}"
    );
}

/// One cell at one version point is one load whatever selects or decodes
/// it: an exact and an indexed selection of the point, and an object- and
/// a function-pointer decoding, intern one `Load` (`design/loads.md`, open
/// question 2), and the cost of the next selection is flat in how many
/// came before.
#[test]
fn one_load_per_cell_regardless_of_exactness_or_type() {
    const TYPES: [ProgramType; 4] = [
        ProgramType::Int32Pointer,
        ProgramType::UInt8Pointer,
        ProgramType::Pointer,
        ProgramType::FunctionPointer(CallbackSignature::UNSPECIFIED),
    ];
    let slot = Address {
        base: AddressBase::Concrete("local:load-slot".into()),
        offset: AddressOffset::Constant(0),
    };
    let mut samples = Vec::new();
    for reads in [4usize, 64, 512] {
        let _session = crate::kernel::VerificationSession::enter();
        let start = ExecutionState::new()
            .with_memory(SymbolicMemory::new().with_block(slot.base.clone(), 8));
        let written = start.clone().with_memory(start.memory().clone().store(
            slot.clone(),
            ProgramValue::Pointer(Pointer::new(
                Address::symbolic(Variable(984_001)),
                ProgramType::Int32Pointer,
            )),
        ));
        let point = written.program_point();
        let indexed = point
            .indexed_typed_version(&slot, ProgramType::Int32Pointer)
            .expect("the store's version");
        assert_eq!(
            indexed.read_key(),
            point.clone().for_exact_read().read_key()
        );
        let before = interned_load_count();
        let first = Load::at(indexed.clone(), &slot);
        for read in 0..reads {
            let selection = if read % 2 == 0 {
                point.clone().for_exact_read()
            } else {
                indexed.clone()
            };
            let ty = TYPES[read % TYPES.len()];
            let value = Pointer::from_point_read(selection, ty, &slot);
            assert_eq!(value.address(), &first.address(), "read {read} at {ty:?}");
            assert_eq!(value.program_type(), ty, "the term keeps its own type");
        }
        assert_eq!(interned_load_count() - before, 1, "one cell is one load");
        let (next, work) = crate::instrumentation::measure_deterministic_work(|| {
            Load::at(point.clone().for_exact_read(), &slot)
        });
        assert_eq!(next, first);
        samples.push(work);
    }
    assert!(
        samples.iter().all(|&work| work == samples[0]),
        "{samples:?}"
    );
}
