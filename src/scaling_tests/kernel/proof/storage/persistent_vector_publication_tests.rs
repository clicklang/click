// Scaling tests of `src/kernel/proof/storage.rs` (module `persistent_vector_publication_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

// Repeated large sibling blocks must keep bounded node work rather than copying a growing prefix.
#[test]
fn terminal_vector_blocks_share_payloads_and_bound_node_work() {
    for prepend in [false, true] {
        for groups in [4_usize, 8, 16, 32] {
            let copies = Arc::new(AtomicUsize::new(0));
            let (published, work) = crate::instrumentation::measure_deterministic_work(|| {
                let mut published = PersistentVector::default();
                for group in 0..groups {
                    let mut sibling: PersistentVector<_> = (0..128)
                        .map(|offset| Counted {
                            value: group * 128 + offset,
                            copies: copies.clone(),
                        })
                        .collect();
                    let old = published.clone();
                    if prepend {
                        sibling.append_shared(&published);
                        published = sibling;
                    } else {
                        published.append_shared(&sibling);
                    }
                    assert_eq!(old.len(), group * 128);
                }
                published
            });
            let height = (usize::BITS - groups.leading_zeros()) as usize;
            assert!(
                work >= groups - 1 && work <= 8 * groups * height,
                "concatenation work must follow tree height: groups={groups}, work={work}"
            );
            assert_eq!(
                copies.load(Ordering::Relaxed),
                0,
                "concatenation retains immutable payloads: groups={groups}, prepend={prepend}"
            );
            assert!(published.0.entries.height() <= 2 * height);
            for (index, item) in published.iter().enumerate() {
                let group = if prepend {
                    groups - 1 - index / 128
                } else {
                    index / 128
                };
                assert_eq!(item.value, group * 128 + index % 128);
            }
        }
    }
}
