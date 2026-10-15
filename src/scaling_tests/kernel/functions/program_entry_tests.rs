// Scaling tests of `src/kernel/functions/program_entry_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

/// Entering a function that names a global array costs the same whatever
/// the array's declared length. Before runs, every element was materialized
/// as its own cell, named and width-recorded one by one, so a
/// `static char buf[65536]` cost 65,536 cells at every entry.
#[test]
fn a_symbolic_global_array_entry_costs_the_same_whatever_its_length() {
    for element_type in [CType::UInt8, CType::Int32, CType::Int32Pointer] {
        let samples = [8u32, 1_000, 1_000_000].map(|length| {
            crate::kernel::eval::clear_load_variable_registry();
            let function = function_with_global_array(element_type, length);
            let (entry, work) = crate::instrumentation::measure_deterministic_work(|| {
                initialize_c_function_globals(&CState::new(), &function)
            });
            (length, work, entry.memory().cells.representation_len())
        });
        let least = samples
            .iter()
            .map(|(_, work, _)| *work)
            .min()
            .expect("samples");
        let most = samples
            .iter()
            .map(|(_, work, _)| *work)
            .max()
            .expect("samples");
        assert_eq!(
            least, most,
            "{element_type:?} entry work depends on the array's length: {samples:?}"
        );
        assert!(
            samples.iter().all(|(_, _, entries)| *entries == 1),
            "{element_type:?} entry is one run: {samples:?}"
        );
    }
}

/// Entering a function over a global array, collecting the variables its
/// entry state mentions, and one statement's store into an element and read
/// of another cost the same whatever the array's length, and name exactly the
/// elements read. Collecting the entry state's variables used to name every
/// element to find its load variable, so a one-million-element array minted
/// a million load identities at function entry and exhausted the load
/// registry before the first statement.
#[test]
fn a_symbolic_global_array_names_only_the_elements_a_function_reads() {
    for element_type in [CType::UInt8, CType::Int32, CType::Int32Pointer] {
        let width = i64::from(element_type.byte_width());
        let samples = [8u32, 1_000, 1_000_000].map(|length| {
            // Each sample is its own verification, so none reuses another's
            // named loads or memoized answers.
            let _session = crate::kernel::VerificationSession::enter();
            let function = function_with_global_array(element_type, length);
            let registered = crate::kernel::eval::load_variable_registry_len;
            let before_entry = registered();
            let (entry, entry_work) = crate::instrumentation::measure_deterministic_work(|| {
                let entry = initialize_c_function_globals(&CState::new(), &function);
                let mut variables = std::collections::BTreeSet::new();
                crate::kernel::reasoning::collect_c_state_bitvector_variables(
                    &entry,
                    &mut variables,
                );
                entry
            });
            let entry_named = registered() - before_entry;
            let base = CMemory::global_pointer("buf");
            let element = |index: i64| Pointer {
                block: base.block.clone(),
                offset: PointerOffsetTerm::Constant(index * width),
            };
            let before_statement = registered();
            let (read, statement_work) = crate::instrumentation::measure_deterministic_work(|| {
                let stored = entry
                    .memory()
                    .clone()
                    .store(element(5), zero_element(element_type));
                let read = stored.load(&element(6));
                let mut variables = std::collections::BTreeSet::new();
                crate::kernel::reasoning::collect_memory_bitvector_variables(
                    &stored,
                    &mut variables,
                );
                read
            });
            assert!(
                matches!(read, CExpressionOutcome::Value(_)),
                "{element_type:?}[{length}] element 6 reads its entry value: {read:?}"
            );
            let statement_named = registered() - before_statement;
            (
                length,
                entry_work,
                entry_named,
                statement_work,
                statement_named,
            )
        });
        let (_, entry_work, entry_named, statement_work, statement_named) = samples[0];
        assert!(
            samples
                .iter()
                .all(|sample| (sample.1, sample.2, sample.3, sample.4)
                    == (entry_work, entry_named, statement_work, statement_named)),
            "{element_type:?} entry or statement cost depends on the array's length \
             (length, entry work, identities named at entry, statement work, identities \
             named by the statement): {samples:?}"
        );
        assert!(
            statement_named <= 2,
            "{element_type:?} a statement reading one element names at most its load \
             and the stored cell's: {samples:?}"
        );
    }
}

/// Program startup, a load of a written element, of an unwritten one, and
/// a store then a load, cost the same whatever the declared length of the
/// initialized arrays, and every load yields exactly the initializer's (or
/// the store's) value. Startup used to store every element one by one, and
/// partitioning the startup permissions walked every cell.
#[test]
fn an_initialized_array_at_startup_costs_the_same_whatever_its_length() {
    let samples = [8u32, 1_000, 1_000_000].map(|length| {
        let _session = crate::kernel::VerificationSession::enter();
        let function = function_with_initialized_arrays(length, false);
        let (startup, startup_work) = crate::instrumentation::measure_deterministic_work(|| {
            initialize_c_program_storage([function.clone()]).expect("no run limit is installed")
        });
        let buf = CMemory::global_pointer("buf");
        let counts = CMemory::static_pointer("main", "counts");
        let element = |index: u32| buf.offset_by_bytes(index * 4);
        let (loads, load_work) = crate::instrumentation::measure_deterministic_work(|| {
            let memory = startup.memory();
            let stored = memory.clone().store(element(5), int32(9));
            [
                memory.load(&element(2)),
                memory.load(&element(5)),
                memory.load(&element(length - 1)),
                memory.load(&counts),
                memory.load(&counts.offset_by_bytes(length - 1)),
                stored.load(&element(5)),
                stored.load(&element(6)),
            ]
        });
        let value = CExpressionOutcome::Value;
        assert_eq!(
            loads,
            [
                value(int32(7)),
                value(int32(0)),
                value(int32(3)),
                value(uint8(255)),
                value(uint8(0)),
                value(int32(9)),
                value(int32(0)),
            ],
            "[{length}] reads its initializer"
        );
        (
            length,
            startup_work,
            load_work,
            startup.memory().cells.representation_len(),
            startup.resources().facts().len(),
        )
    });
    let (_, startup_work, load_work, entries, facts) = samples[0];
    assert!(
        samples
            .iter()
            .all(|sample| (sample.1, sample.2, sample.3, sample.4)
                == (startup_work, load_work, entries, facts)),
        "startup cost depends on the arrays' length (length, startup work, load work, \
         cell entries, startup permissions): {samples:?}"
    );
}

/// An ordinary function's entry knows a `const` array's contents too, and
/// installs them at the same cost whatever the array's length.
#[test]
fn a_constant_array_at_function_entry_costs_the_same_whatever_its_length() {
    let samples = [8u32, 1_000, 1_000_000].map(|length| {
        let _session = crate::kernel::VerificationSession::enter();
        let function = function_with_initialized_arrays(length, true);
        let (entry, work) = crate::instrumentation::measure_deterministic_work(|| {
            initialize_c_function_globals(&CState::new(), &function)
        });
        let buf = CMemory::global_pointer("buf");
        assert_eq!(
            entry.memory().load(&buf.offset_by_bytes(8)),
            CExpressionOutcome::Value(int32(7)),
            "[{length}] element 2"
        );
        assert_eq!(
            entry.memory().load(&buf.offset_by_bytes(12)),
            CExpressionOutcome::Value(int32(0)),
            "[{length}] element 3"
        );
        (length, work, entry.memory().cells.representation_len())
    });
    assert!(
        samples
            .iter()
            .all(|sample| (sample.1, sample.2) == (samples[0].1, samples[0].2)),
        "constant array entry cost depends on its length (length, work, cell entries): \
         {samples:?}"
    );
}

/// Program startup, and loads of written and zero fields and a store then a
/// load, cost the same whatever the length of an array of structs, and
/// every load is exact. Startup used to store every field of every element.
#[test]
fn an_aggregate_array_at_startup_costs_the_same_whatever_its_length() {
    let samples = [100u32, 10_000, 1_000_000].map(|length| {
        let _session = crate::kernel::VerificationSession::enter();
        let function = function_with_aggregate_arrays(length, 0, false);
        let (startup, startup_work) = crate::instrumentation::measure_deterministic_work(|| {
            initialize_c_program_storage([function.clone()]).expect("no run limit is installed")
        });
        let pool = CMemory::global_pointer("pool");
        let slots = CMemory::static_pointer("main", "slots");
        let field = |element: u32, offset: u32| pool.offset_by_bytes(element * 24 + offset);
        let (loads, load_work) = crate::instrumentation::measure_deterministic_work(|| {
            let memory = startup.memory();
            let stored = memory.clone().store(field(5, 0), int32(9));
            [
                memory.load(&field(2, 0)),
                memory.load(&field(5, 0)),
                memory.load(&field(5, 8)),
                memory.load(&field(length - 1, 20)),
                memory.load(&field(length - 1, 16)),
                memory.load(&slots.offset_by_bytes(4)),
                memory.load(&slots.offset_by_bytes((length - 1) * 24 + 4)),
                stored.load(&field(5, 0)),
                stored.load(&field(6, 0)),
            ]
        });
        let value = CExpressionOutcome::Value;
        assert_eq!(
            loads,
            [
                value(int32(7)),
                value(int32(0)),
                value(CValue::typed_pointer(Pointer::null(), CType::Int32Pointer)),
                value(int32(3)),
                value(int32(0)),
                value(uint8(255)),
                value(uint8(0)),
                value(int32(9)),
                value(int32(0)),
            ],
            "[{length}] reads its initializer"
        );
        (
            length,
            startup_work,
            load_work,
            startup.memory().cells.representation_len(),
            startup.resources().facts().len(),
        )
    });
    let (_, startup_work, load_work, entries, facts) = samples[0];
    assert!(
        samples
            .iter()
            .all(|sample| (sample.1, sample.2, sample.3, sample.4)
                == (startup_work, load_work, entries, facts)),
        "startup cost depends on the aggregate arrays' length (length, startup work, load \
         work, cell entries, startup permissions): {samples:?}"
    );
}

/// An ordinary function's entry, and loads of its fields, cost the same
/// whatever the length of a symbolic array of structs, and name no field it
/// does not read. Entry used to name every field of every struct, so a
/// million-struct pool exhausted the load identities.
#[test]
fn a_symbolic_aggregate_array_at_function_entry_costs_the_same_whatever_its_length() {
    let samples = [100u32, 10_000, 1_000_000].map(|length| {
        let _session = crate::kernel::VerificationSession::enter();
        let function = function_with_aggregate_arrays(length, 0, false);
        let registered = crate::kernel::eval::load_variable_registry_len();
        let (entry, entry_work) = crate::instrumentation::measure_deterministic_work(|| {
            initialize_c_function_globals(&CState::new(), &function)
        });
        let pool = CMemory::global_pointer("pool");
        let (loads, load_work) = crate::instrumentation::measure_deterministic_work(|| {
            [
                entry.memory().load(&pool.offset_by_bytes(24 * 7)),
                entry
                    .memory()
                    .load(&pool.offset_by_bytes(24 * (length - 1) + 20)),
            ]
        });
        assert!(
            loads.iter().all(|load| matches!(
                load,
                CExpressionOutcome::Value(CValue::Int32(Bitvector32Term::Variable(_)))
            )),
            "[{length}] a field reads as its load: {loads:?}"
        );
        (
            length,
            entry_work,
            load_work,
            entry.memory().cells.representation_len(),
            crate::kernel::eval::load_variable_registry_len() - registered,
        )
    });
    let (_, entry_work, load_work, entries, named) = samples[0];
    assert!(
        samples
            .iter()
            .all(|sample| (sample.1, sample.2, sample.3, sample.4)
                == (entry_work, load_work, entries, named)),
        "a symbolic aggregate array's entry depends on its length (length, entry work, load \
         work, cell entries, load identities named): {samples:?}"
    );
}
