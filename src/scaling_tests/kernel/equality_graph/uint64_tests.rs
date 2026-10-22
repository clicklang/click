// Scaling tests of `src/kernel/equality_graph/uint64_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn integer_address_queries_ignore_unrelated_equations_and_reuse_definitions() {
    let _session = VerificationSession::enter();
    let mut samples = Vec::new();
    for size in [16_u64, 64, 256, 1024] {
        let mut graph = EqualityGraph::default();
        for i in 0..size {
            graph.add_uint64_equality(
                &Bitvector32Term::Variable(Variable(i)),
                &Bitvector32Term::Variable(Variable(i + 10_000)),
            );
        }
        let bits = Bitvector32Term::Variable(Variable(960_004));
        let decoded = Pointer::integer_address(bits.clone());
        assert!(graph.are_uint64_equal(&raw_address(&decoded), &bits));
        let (((), work), maps) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..16 {
                    assert!(graph.are_uint64_equal(&raw_address(&decoded), &bits));
                }
            })
        });
        samples.push((work, maps));
    }
    assert!(
        samples
            .windows(2)
            .all(|p| p[0].0 == p[1].0 && p[1].1 <= p[0].1 * 2),
        "{samples:?}"
    );
}

#[test]
fn wide_congruence_queries_do_not_scan_unrelated_equalities() {
    let mut previous = None;
    for size in [16_u64, 64, 256, 1024] {
        let _session = VerificationSession::enter();
        let p = Pointer::symbolic(Variable(940_001));
        let q = Pointer::symbolic(Variable(940_002));
        let a = Bitvector32Term::Variable(Variable(940_003));
        let b = Bitvector32Term::Variable(Variable(940_004));
        let mut graph = EqualityGraph::default();
        for i in 0..size {
            graph.add_uint64_equality(
                &Bitvector32Term::Variable(Variable(i)),
                &Bitvector32Term::Variable(Variable(i + 10_000)),
            );
        }
        graph.add_uint64_equality(&a, &packed(&b, &p));
        graph.add_equality(&p, &q);
        let (ok, work) = crate::instrumentation::measure_deterministic_work(|| {
            graph.are_uint64_equal(&a, &packed(&b, &q))
        });
        assert!(ok);
        if let Some(previous) = previous {
            assert_eq!(
                work, previous,
                "unrelated facts changed query work at {size}"
            );
        }
        previous = Some(work);
    }
}

#[test]
fn range_values_and_constants_resolve_long_wide_equality_chains() {
    use crate::kernel::{ConditionTerm, PureFactContext};
    for size in [16u64, 64, 256, 1024] {
        let _session = VerificationSession::enter();
        let var = |i| Bitvector32Term::Variable(Variable(950_000 + i));
        let mut facts = PureFactContext::new();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            for i in 0..size {
                facts = facts
                    .clone()
                    .assume_condition(ConditionTerm::uint64_equal(var(i), var(i + 1)), true);
            }
            facts = facts.clone().assume_condition(
                ConditionTerm::uint64_equal(var(size), Bitvector32Term::UInt64Constant(37)),
                true,
            );
            assert_eq!(facts.wide_constant_from_equalities(&var(0)), Some(37));
            assert!(facts.uint64_values_equal_for_range_resolution(
                &var(0),
                &Bitvector32Term::UInt64Constant(37)
            ));
        });
        assert!(work < 300 * size as usize, "size={size}, work={work}");
    }
}

#[test]
fn an_aliased_read_meets_its_stored_cell_without_scanning_unrelated_cells_or_aliases() {
    let mut previous = None;
    for size in [16_u64, 64, 256, 1024] {
        let _session = VerificationSession::enter();
        let mut memory = CMemory::new().with_block("cells", 8 * (size as u32 + 1));
        let cell = |i: u64| Pointer {
            block: "cells".into(),
            offset: PointerOffsetTerm::Constant(8 * i as i64),
        };
        for i in 0..=size {
            memory = memory.store(cell(i), CValue::UInt64(Bitvector32Term::UInt64Constant(i)));
        }
        let memory = intern_c_memory(memory);
        let mut context = PureFactContext::new();
        for i in 0..size {
            let other = Pointer::symbolic(Variable(970_000 + i));
            context = context.assume_proposition(alias(&other, &cell(i)));
        }
        let read_at = Pointer::symbolic(Variable(979_999));
        context = context.assume_proposition(alias(&read_at, &cell(size)));
        let read = word(&memory, &read_at, 8);
        let stored = Bitvector32Term::UInt64Constant(size);
        let (ok, work) = crate::instrumentation::measure_deterministic_work(|| {
            context.equality_graph.are_uint64_equal(&read, &stored)
        });
        assert!(ok);
        if let Some(previous) = previous {
            assert_eq!(
                work, previous,
                "unrelated cells or aliases changed work at {size}"
            );
        }
        previous = Some(work);
    }
}

#[test]
fn an_aliased_read_grows_linearly_with_its_own_alias_class() {
    let mut samples = Vec::new();
    for size in [16_u64, 64, 256, 1024] {
        let _session = VerificationSession::enter();
        let stored_at = Pointer {
            block: "cells".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let memory = intern_c_memory(CMemory::new().with_block("cells", 8).store(
            stored_at.clone(),
            CValue::UInt64(Bitvector32Term::UInt64Constant(7)),
        ));
        let mut context = PureFactContext::new();
        let link = |i: u64| Pointer::symbolic(Variable(972_000 + i));
        context = context.assume_proposition(alias(&link(0), &stored_at));
        for i in 1..=size {
            context = context.assume_proposition(alias(&link(i), &link(i - 1)));
        }
        let read = word(&memory, &link(size), 8);
        let (ok, work) = crate::instrumentation::measure_deterministic_work(|| {
            context
                .equality_graph
                .are_uint64_equal(&read, &Bitvector32Term::UInt64Constant(7))
        });
        assert!(ok);
        samples.push((size, work));
    }
    // Linear in the class: four times the aliases, at most about four times
    // the work.
    assert!(
        samples.windows(2).all(|pair| pair[1].1 <= pair[0].1 * 5),
        "{samples:?}"
    );
}

#[test]
fn a_late_alias_rechecks_only_the_reads_of_its_own_address_class() {
    let mut unrelated = None;
    let mut related = Vec::new();
    for size in [16_u64, 64, 256] {
        let _session = VerificationSession::enter();
        let read_at = Pointer::symbolic(Variable(973_000));
        let mut memory = CMemory::new().with_block("other", 8 * size as u32);
        let mut graph = EqualityGraph::default();
        // One unresolved read of `read_at` in each of `size` snapshots.
        for i in 0..size {
            memory = memory.store(
                Pointer {
                    block: "other".into(),
                    offset: PointerOffsetTerm::Constant(8 * i as i64),
                },
                CValue::UInt64(Bitvector32Term::UInt64Constant(i)),
            );
            let read = word(&intern_c_memory(memory.clone()), &read_at, 8);
            assert!(!graph.are_uint64_equal(&read, &Bitvector32Term::UInt64Constant(99)));
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            graph.add_equality(
                &Pointer::symbolic(Variable(974_000)),
                &Pointer::symbolic(Variable(974_001)),
            );
        });
        if let Some(previous) = unrelated {
            assert_eq!(work, previous, "an unrelated alias changed work at {size}");
        }
        unrelated = Some(work);
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            graph.add_equality(&Pointer::symbolic(Variable(974_002)), &read_at);
            graph.are_uint64_equal(
                &Bitvector32Term::UInt64Constant(1),
                &Bitvector32Term::UInt64Constant(1),
            );
        });
        related.push((size, work));
    }
    // Linear in the class's reads: four times the reads, about four times
    // the work.
    assert!(
        related.windows(2).all(|pair| pair[1].1 <= pair[0].1 * 5),
        "{related:?}"
    );
}
