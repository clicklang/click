use super::*;
use std::cell::Cell;

#[test]
fn declaration_identity_survives_duplicates_missing_facts_and_guard_facts() {
    let declarations = [3, 3, 8, 9, 9];
    let emitted = [42, 9, 3, 17];
    assert_eq!(
        retained_loop_invariant_declarations(declarations.iter(), emitted.iter()),
        [(0, &3), (1, &3), (3, &9), (4, &9)],
    );
}

#[test]
fn loop_invariant_correspondence_has_output_logarithmic_indexing_cost() {
    #[derive(Eq)]
    struct Counted<'a>(usize, &'a Cell<usize>);
    impl PartialEq for Counted<'_> {
        fn eq(&self, other: &Self) -> bool {
            self.cmp(other).is_eq()
        }
    }
    impl PartialOrd for Counted<'_> {
        fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
            Some(self.cmp(other))
        }
    }
    impl Ord for Counted<'_> {
        fn cmp(&self, other: &Self) -> std::cmp::Ordering {
            self.1.set(self.1.get() + 1);
            self.0.cmp(&other.0)
        }
    }
    for size in [32usize, 128, 512, 2048] {
        let comparisons = Cell::new(0);
        let declarations = (0..size)
            .flat_map(|i| [Counted(i, &comparisons), Counted(i, &comparisons)])
            .collect::<Vec<_>>();
        let facts = (0..size)
            .rev()
            .map(|i| Counted(i, &comparisons))
            .collect::<Vec<_>>();
        let retained = retained_loop_invariant_declarations(declarations.iter(), facts.iter());
        assert_eq!(retained.len(), size * 2);
        assert!(
            comparisons.get() <= 16 * size * (size.ilog2() as usize + 1),
            "size {size}: {} comparisons",
            comparisons.get()
        );
    }
}
