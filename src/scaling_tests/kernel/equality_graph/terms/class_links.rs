use super::*;

#[test]
fn class_links_fork_writes_copy_only_selected_pages() {
    let page_len = PAGE_LEN as u64;
    let first = 0;
    let moved = 1;
    let second = page_len;
    let missing = u64::MAX - 1;

    for pages in [64, 256, 1024, 4096] {
        let mut ancestor = ClassLinks::default();
        for page in 0..pages {
            ancestor.set_weight(page * page_len, 2);
        }
        ancestor.set_weight(moved, 3);
        assert!(!ancestor.has_parents());

        let mut left = ancestor.clone();
        let mut right = ancestor.clone();
        assert!(
            ancestor
                .pages
                .values()
                .all(|page| Arc::strong_count(page) == 1)
        );

        left.merge(moved, first, 5);
        right.merge(moved, second, 5);
        assert!(left.has_parents());
        assert!(right.has_parents());
        assert!(!ancestor.has_parents());
        assert_eq!(left.parent(moved), Some(first));
        assert_eq!(right.parent(moved), Some(second));
        assert_eq!(ancestor.parent(moved), None);
        assert_eq!(left.weight(moved), 1);
        assert_eq!(right.weight(moved), 1);
        assert_eq!(ancestor.weight(moved), 3);
        assert_eq!((left.weight(first), left.weight(second)), (5, 2));
        assert_eq!((right.weight(first), right.weight(second)), (2, 5));
        assert_eq!((ancestor.weight(first), ancestor.weight(second)), (2, 2));

        // Only the mutated pages should have new allocations. The copied
        // directory paths can clone some adjacent Arc handles, independent
        // of how many unrelated pages the parent retains.
        let copied = |branch: &ClassLinks| {
            ancestor
                .pages
                .iter()
                .filter(|(id, page)| !Arc::ptr_eq(page, branch.pages.get(*id).unwrap()))
                .count()
        };
        assert_eq!(copied(&left), 1);
        assert_eq!(copied(&right), 2);
        let cloned_handles = ancestor
            .pages
            .values()
            .filter(|page| Arc::strong_count(page) > 1)
            .count();
        assert!(
            cloned_handles <= 128,
            "pages={pages}, cloned handles={cloned_handles}"
        );

        assert_eq!(right.parent(missing), None);
        assert_eq!(right.weight(missing), 1);
        right.merge(missing, second, 6);
        assert_eq!(right.parent(missing), Some(second));
        assert_eq!(right.pages.len(), ancestor.pages.len() + 1);
        assert_eq!(ancestor.parent(missing), None);
    }
}
