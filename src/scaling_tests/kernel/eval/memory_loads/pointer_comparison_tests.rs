use super::*;

#[test]
fn stored_pointer_block_queries_scale_with_new_read_definitions() {
    fn work(steps: u64, unrelated: u64) -> usize {
        let _session = VerificationSession::enter();
        let target = Pointer {
            block: PointerBlock::Heap(989_010),
            offset: PointerOffsetTerm::Constant(0),
        };
        let other = PointerBlock::Heap(989_011);
        let slot = Pointer::symbolic(Variable(989_012));
        let mut memory = CMemory::new()
            .with_block(target.block.clone(), 8)
            .with_block(other.clone(), 8);
        for index in 0..unrelated {
            memory = memory.store(
                Pointer::symbolic(Variable(990_000 + index)),
                CValue::Int32(0u32.into()),
            );
        }
        let mut pointer = target;
        let mut reads = Vec::new();
        for _ in 0..steps {
            memory = memory.clone().store(
                slot.clone(),
                CValue::typed_pointer(pointer, CType::Int32Pointer),
            );
            pointer = Pointer::loaded_value(&intern_c_memory_ref(&memory), &slot);
            reads.push(pointer.clone());
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for read in &reads {
                assert!(read.block.proven_distinct(&other));
            }
        });
        work
    }
    let costs = [4, 8, 16, 32].map(|steps| work(steps, 0));
    assert!(costs[0] > 0);
    assert!(costs.windows(2).all(|p| p[1] <= 3 * p[0]), "{costs:?}");
    let unrelated_costs = [0, 8, 32, 128].map(|unrelated| work(8, unrelated));
    assert!(
        unrelated_costs
            .iter()
            .all(|cost| *cost == unrelated_costs[0]),
        "{unrelated_costs:?}"
    );
}
