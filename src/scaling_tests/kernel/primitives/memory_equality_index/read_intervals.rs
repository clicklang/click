use super::super::AffineOffset;
use super::*;

#[test]
fn selecting_one_overlap_never_enumerates_the_interval_population() {
    let coordinate = |n| AddressCoordinate(AffineOffset::constant(n));
    for dense in [false, true] {
        let mut samples = Vec::new();
        for size in [16_u64, 64, 256, 1024] {
            let mut intervals = ReadIntervals::default();
            for entry in 0..size {
                let start = if dense { 0 } else { i128::from(entry) * 4 };
                intervals.insert(coordinate(start), coordinate(start + 2), entry);
            }
            let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
                assert!(
                    intervals
                        .first_overlap(&coordinate(0), &coordinate(1))
                        .is_some()
                );
                assert!(
                    intervals
                        .first_overlap(&coordinate(2), &coordinate(4))
                        .is_none()
                );
                assert!(
                    intervals
                        .first_overlap(&coordinate(-4), &coordinate(-2))
                        .is_none()
                );
            });
            samples.push(work);
        }
        assert!(
            samples.iter().all(|work| *work <= samples[0] + 24),
            "dense={dense}: {samples:?}"
        );
    }
}
