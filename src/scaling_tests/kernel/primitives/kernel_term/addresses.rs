use super::*;

#[test]
fn address_construction_and_identity_do_not_walk_displacement_dags() {
    for unrelated in [0, 128, 512] {
        let _unrelated = (0..unrelated)
            .map(|i| SharedPointerBlock::import(&PointerBlock::Heap(i)))
            .collect::<Vec<_>>();
        let block = SharedPointerBlock::import(&PointerBlock::Symbolic(Variable(999001)));
        for size in [16, 64, 256] {
            let mut offset = KernelPointerOffset::Constant(0).into_shared().unwrap();
            for _ in 0..size {
                offset = KernelPointerOffset::Add([offset.clone(), offset])
                    .into_shared()
                    .unwrap();
            }
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                let a = SharedPointerAddress::new(block.clone(), offset.clone());
                let b = SharedPointerAddress::new(block.clone(), offset.clone());
                assert_eq!(a, b);
                let mut hash = std::collections::hash_map::DefaultHasher::new();
                a.hash(&mut hash);
                assert_eq!(a.node().offset, offset);
            });
            assert_eq!(work, 2, "size={size}, unrelated={unrelated}");
        }
    }
}

#[test]
fn block_import_charges_selected_bytes_not_unrelated_literal_bytes() {
    for size in [16, 64, 256] {
        let _unrelated = (0..size)
            .map(|i| {
                SharedPointerBlock::import(&PointerBlock::StringLiteral {
                    identity: format!("unrelated-{i}"),
                    bytes: vec![0; size * 16],
                })
            })
            .collect::<Vec<_>>();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            SharedPointerBlock::import(&PointerBlock::Symbolic(Variable(999002)))
        });
        assert_eq!(work, 9);
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            SharedPointerBlock::import(&PointerBlock::Concrete("x".repeat(size)))
        });
        assert_eq!(work, 9 + size);
    }
}
