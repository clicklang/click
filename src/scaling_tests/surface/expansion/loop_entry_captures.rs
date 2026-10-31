fn entry_tree(start: usize, end: usize) -> LoopEntryBranches {
    if end - start == 1 {
        return LoopEntryBranches::Leaf(vec![start]);
    }
    let middle = (start + end) / 2;
    LoopEntryBranches::Split {
        condition: ClickProposition::PredicateCall {
            name: format!("guard_{start}_{end}"),
            arguments: vec![],
        },
        yes: Box::new(entry_tree(start, middle)),
        no: Box::new(entry_tree(middle, end)),
    }
}

#[test]
fn loop_entry_capture_work_tracks_emitted_branches() {
    for size in [2, 4, 8, 16, 32] {
        let tree = entry_tree(0, size);
        let paths = (0..size)
            .map(|i| Some(Ok(vec![ProofTactic::Mark(format!("path_{i}"))])))
            .collect::<Vec<_>>();
        let (expanded, work) = crate::instrumentation::measure_deterministic_work(|| {
            guarded_entry_expansion(&tree, &paths).unwrap().unwrap()
        });
        assert_eq!(work, 3 * size - 1);
        let mut pending = vec![expanded.as_slice()];
        let mut leaves = 0;
        while let Some(tactics) = pending.pop() {
            match tactics {
                [ProofTactic::If(branch)] => {
                    pending.push(&branch.then_tactics);
                    pending.push(&branch.else_tactics);
                }
                [ProofTactic::Mark(_)] => leaves += 1,
                _ => panic!("unexpected entry certificate"),
            }
        }
        assert_eq!(leaves, size);
    }
}
