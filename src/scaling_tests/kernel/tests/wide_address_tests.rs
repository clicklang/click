// Scaling tests of `src/kernel/tests/wide_address_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn wide_address_symbolic_array_runs_keep_typed_loads_and_bounded_work() {
    for ty in [CType::Int128, CType::UInt128] {
        let mut samples = Vec::new();
        for count in [16, 64, 256, 1024, 1_000_000] {
            let _session = crate::kernel::VerificationSession::enter();
            let base = CMemory::global_pointer("wide-run");
            let at = |index| base.offset_by_bytes(index * 16);
            let zero = value(
                &CState::new(),
                if ty == CType::Int128 {
                    c_int128_literal(0)
                } else {
                    c_uint128_literal(0)
                },
            );
            let function = c_function(
                CType::Int32,
                "wide_array",
                vec![],
                c_return(c_int32_literal(0)),
            )
            .with_global_arrays(vec![CGlobalArray::new_with_kernel_name(
                "wide-run",
                "wide-run",
                ty,
                count,
                CArrayContents::new(count, zero, []),
            )]);
            let (entry, setup_work) = crate::instrumentation::measure_deterministic_work(|| {
                initialize_c_function_globals(&CState::new(), &function)
            });
            let memory = entry.memory.clone();
            assert_eq!(memory.cells.representation_len(), 1);
            let (loaded, read_work) = crate::instrumentation::measure_deterministic_work(|| {
                memory.known_value(&at(count - 1)).unwrap()
            });
            assert_eq!(loaded.c_type(), ty);
            let machine = MachineIntegerType::from_c_type(ty).unwrap();
            assert!(machine.accepts_wide_term(&c_value_bitvector_term(&loaded).unwrap()));
            assert_eq!(loaded, memory.known_value(&at(count - 1)).unwrap());
            let state = CState::new()
                .with_memory(memory.clone())
                .with_resource_context(ResourceContext::new().unchecked_with_facts([
                    CResourceFact::view_memory(CMemoryRange::new_with_element_width(
                        at(count - 1),
                        0u32.into(),
                        1u32.into(),
                        16,
                    )),
                ]));
            assert_eq!(
                value(
                    &state,
                    c_typed_load(
                        c_typed_pointer_value(at(count - 1), ty.pointer_to().unwrap()),
                        ty
                    )
                ),
                loaded
            );
            let replacement = value(
                &CState::new(),
                if ty == CType::Int128 {
                    c_int128_literal(i128::MIN)
                } else {
                    c_uint128_literal(u128::MAX)
                },
            );
            let changed = memory
                .without_possible_aliasing_cells(&at(count - 1), 16, &PureFactContext::new())
                .store(at(count - 1), replacement.clone());
            assert_eq!(changed.known_value(&at(count - 1)), Some(replacement));
            assert!(changed.known_value(&at(count - 2)).is_some());
            samples.push(setup_work + read_work);
        }
        assert!(samples.iter().all(|work| *work < 4096), "{samples:?}");
        assert!(
            samples.iter().max().unwrap() - samples.iter().min().unwrap() <= 128,
            "{samples:?}"
        );
    }
}
