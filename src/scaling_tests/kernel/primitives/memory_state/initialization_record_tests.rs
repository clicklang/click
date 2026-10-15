// Scaling tests of `src/kernel/primitives/memory_state.rs` (module `initialization_record_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn a_declared_object_makes_dropping_its_runs_one_query() {
    // With the declaration's object recorded, a havoc dropping its runs
    // costs the runs, not their slots, whatever the struct count.
    let mut works = Vec::new();
    for count in [1_000u32, 10_000, 100_000] {
        let block = format!("local:record-declared-{count}");
        let memory =
            zero_runs(&block, count, 8).with_initialized_object(&element(&block, 0), count * 8);
        let (havoc, work) =
            crate::instrumentation::measure_deterministic_work(|| loop_havoc(memory, 924_006));
        assert!(havoc.has_initialized_bytes_at(&element(&block, 0), count * 8));
        works.push(work);
    }
    assert!(
        works.windows(2).all(|pair| pair[0] == pair[1]),
        "dropping declared runs cost {works:?} work units"
    );
}

#[test]
fn a_covering_query_scales_with_the_cells_it_crosses() {
    // A read bounded to two elements of an array whose every element is
    // a cached cell costs those two cells, whatever the array's size.
    let mut works = Vec::new();
    for count in [64i64, 512, 4096] {
        let block = format!("local:record-cells-{count}");
        let mut memory =
            CMemory::new().with_block(block.as_str(), u32::try_from(4 * count).unwrap());
        for index in 0..count {
            memory = memory.store(
                element(&block, index),
                CValue::Int32(Bitvector32Term::Constant(1)),
            );
        }
        let index = Bitvector32Term::Variable(Variable(924_008));
        let read = Pointer {
            block: PointerBlock::from(block.as_str()),
            offset: PointerOffsetTerm::scale_int32(index.clone(), 4),
        };
        let assumptions = index_between(&index, 7, 8);
        let (covered, work) = crate::instrumentation::measure_deterministic_work(|| {
            memory.has_initialized_bytes_under(&read, 4, &assumptions)
        });
        assert!(covered);
        works.push(work);
    }
    assert!(
        works.windows(2).all(|pair| pair[0] == pair[1]),
        "covering queries cost {works:?} work units"
    );
}
