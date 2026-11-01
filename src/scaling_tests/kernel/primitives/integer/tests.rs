// Scaling tests of `src/kernel/primitives/integer.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn exact_integer_numeric_work_has_explicit_size_scaling() {
    let mut additions = Vec::new();
    let mut products = Vec::new();
    for bits in [64usize, 128, 256, 512] {
        let magnitude = BigInt::one() << bits;
        let (sum, add_work) = crate::instrumentation::measure_deterministic_work(|| {
            IntegerTerm::add(
                IntegerTerm::constant(magnitude.clone()),
                IntegerTerm::constant(-&magnitude - 7),
            )
        });
        assert_eq!(sum.as_const(), Some(&BigInt::from(-7)));
        let (product, product_work) = crate::instrumentation::measure_deterministic_work(|| {
            IntegerTerm::multiply(
                IntegerTerm::constant(magnitude.clone()),
                IntegerTerm::constant(-&magnitude),
            )
        });
        assert_eq!(product.as_const(), Some(&-(BigInt::one() << (2 * bits))));
        additions.push(add_work);
        products.push(product_work);
    }
    for pair in additions.windows(2) {
        assert!(pair[1] > pair[0]);
        assert!(
            pair[1] <= 2 * pair[0] + 8,
            "addition charges linear numeric work"
        );
    }
    for pair in products.windows(2) {
        assert!(
            pair[1] > 3 * pair[0],
            "multiplication must not charge only operand lengths"
        );
        assert!(
            pair[1] <= 4 * pair[0] + 8,
            "the conservative product allowance scales by bit products"
        );
    }
}

#[test]
fn truncating_integer_congruence_visits_shared_nodes_once() {
    for depth in [2usize, 8, 32, 128] {
        let from: SharedIntegerTerm = IntegerTerm::var(Variable(84)).into();
        let to: SharedIntegerTerm = IntegerTerm::var(Variable(85)).into();
        let mut term = from.clone();
        for level in 0..depth {
            term = if level % 2 == 0 {
                IntegerTerm::TruncatingQuotient(term.clone(), term).into()
            } else {
                IntegerTerm::TruncatingRemainder(term.clone(), term).into()
            };
        }
        let goal = Proposition::ConditionIs(ConditionTerm::IntegerEqual(term.clone(), term), true);
        let (rewritten, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::substitute_integer_term_in_proposition(&goal, &from, &to).unwrap()
        });
        assert!(work <= 4 * depth + 8, "depth={depth}, work={work}");
        let Proposition::ConditionIs(ConditionTerm::IntegerEqual(left, right), true) = rewritten
        else {
            unreachable!()
        };
        assert_eq!(left.id(), right.id());
        let mut node = left;
        for _ in 0..depth {
            let (left, right) = match node.as_ref() {
                IntegerTerm::TruncatingQuotient(a, b) | IntegerTerm::TruncatingRemainder(a, b) => {
                    (a, b)
                }
                _ => unreachable!(),
            };
            assert_eq!(left.id(), right.id());
            node = left.clone();
        }
        assert_eq!(node, to);
    }
}

#[test]
fn truncating_integer_constant_work_scales_with_operand_bits() {
    let mut work = Vec::new();
    for bits in [64usize, 128, 256, 512] {
        let a: BigInt = (BigInt::one() << bits) + 7;
        let b: BigInt = (BigInt::one() << (bits / 2)) + 1;
        let (_, charged) = crate::instrumentation::measure_deterministic_work(|| {
            IntegerTerm::truncating_quotient(
                IntegerTerm::constant(a.clone()),
                IntegerTerm::constant(b.clone()),
            )
        });
        work.push(charged);
    }
    for pair in work.windows(2) {
        assert!(pair[1] > 3 * pair[0]);
        assert!(pair[1] <= 4 * pair[0] + 16);
    }
}

/// `n` observations of `int32` widenings of distinct `uint8` variables, and
/// the same observations read through rule W, each summed left to right.
fn widened_and_read_sums(n: u32) -> (SharedIntegerTerm, SharedIntegerTerm) {
    let mut widened: Option<SharedIntegerTerm> = None;
    let mut read: Option<SharedIntegerTerm> = None;
    for k in 0..n {
        let byte = Bitvector32Term::Variable(Variable(940_000 + u64::from(k)));
        let widening = Bitvector32Term::MachineIntegerCast {
            value: Box::new(byte.clone()),
            source: MachineIntegerType::UInt8,
            destination: MachineIntegerType::Int32,
        };
        let observed: SharedIntegerTerm =
            IntegerTerm::from_machine(MachineIntegerType::Int32, widening)
                .expect("a widening has an observation")
                .into();
        let original: SharedIntegerTerm =
            IntegerTerm::from_machine(MachineIntegerType::UInt8, byte)
                .expect("a byte has an observation")
                .into();
        assert_ne!(observed, original, "the observation keeps its widening");
        widened = Some(match widened {
            Some(sum) => IntegerTerm::Add(sum, observed).into(),
            None => observed,
        });
        read = Some(match read {
            Some(sum) => IntegerTerm::Add(sum, original).into(),
            None => original,
        });
    }
    (widened.expect("n > 0"), read.expect("n > 0"))
}

/// Rule W's reading of a term through its observations' widenings is
/// computed once per node: the first reading of an `n`-term sum costs the
/// same work per term at every size, and every later reading, and every
/// identity, hash and order of a comparison over it, costs none.
#[test]
fn widening_value_reading_is_constant_per_node_and_cached() {
    use std::hash::{Hash, Hasher};
    let hash = |condition: &ConditionTerm| {
        let mut state = std::collections::hash_map::DefaultHasher::new();
        condition.hash(&mut state);
        state.finish()
    };
    let mut first = Vec::new();
    let mut identities = Vec::new();
    for n in [16u32, 64, 256, 1024] {
        let (widened, read) = widened_and_read_sums(n);
        let (reading, work) =
            crate::instrumentation::measure_deterministic_work(|| widened.read_through());
        assert_eq!(reading, read, "n={n}");
        first.push((n, work));
        let (_, again) =
            crate::instrumentation::measure_deterministic_work(|| widened.read_through());
        assert_eq!(again, 0, "n={n}: a second reading is cached");
        let bound = |value: SharedIntegerTerm| {
            ConditionTerm::IntegerLessEqual(value, IntegerTerm::constant_i64(7).into())
        };
        let (written, stated) = (bound(widened.clone()), bound(read.clone()));
        let (same, identity_work) = crate::instrumentation::measure_deterministic_work(|| {
            written == stated
                && written.cmp(&stated) == std::cmp::Ordering::Equal
                && hash(&written) == hash(&stated)
        });
        assert!(same, "n={n}: one fact up to rule W");
        identities.push(identity_work);
    }
    // The identity reads cached readings: only the shared constant side is
    // read once, at every size.
    assert!(
        identities
            .iter()
            .all(|work| *work == identities[0] && *work <= 2),
        "{identities:?}"
    );
    // One node visit per node of the widened sum (each observation and each
    // sum node); the read sum's nodes are their own readings and are not
    // revisited. Exactly linear: the same work per added term.
    assert_linear(&first);
}

/// Each step between sizes costs the same work per added term.
fn assert_linear(costs: &[(u32, usize)]) {
    let rate = |(small, small_work): (u32, usize), (large, large_work): (u32, usize)| {
        assert!(large_work >= small_work, "{costs:?}");
        ((large_work - small_work) as f64) / f64::from(large - small)
    };
    let first = rate(costs[0], costs[1]);
    assert!(first >= 1.0, "{costs:?}");
    for pair in costs.windows(2).skip(1) {
        assert!((rate(pair[0], pair[1]) - first).abs() < 1e-9, "{costs:?}");
    }
}

/// The Integer engines read an observation through rule W at its atom, so
/// `sum(to_integer(widen(v_k))) == sum(to_integer(v_k))` is the trivial claim,
/// in work linear in the number of terms.
#[test]
fn widened_observations_are_one_affine_atom_with_their_operands() {
    let mut costs = Vec::new();
    for n in [16u32, 64, 256, 1024] {
        let (widened, read) = widened_and_read_sums(n);
        let equality = Proposition::ConditionIs(ConditionTerm::IntegerEqual(widened, read), true);
        let (claim, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::proof::integer_arithmetic::integer_affine_claim(&equality)
        });
        let claim = claim.expect("an affine claim");
        assert!(claim.terms.is_empty(), "n={n}: {claim:?}");
        assert!(claim.constant.is_zero(), "n={n}");
        costs.push((n, work));
    }
    assert_linear(&costs);
}
