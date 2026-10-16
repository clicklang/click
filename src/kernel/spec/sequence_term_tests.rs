use super::*;

fn singleton(value: u32) -> SequenceTerm {
    SequenceTerm {
        element_type: Some(CType::Int32),
        node: std::sync::Arc::new(SequenceTermNode::Literal(vec![int32(value)].into())),
    }
}

#[test]
fn integer_sequence_equality_has_linear_size_and_logarithmic_depth() {
    for size in [8usize, 32, 128, 512] {
        let mut left = singleton(0);
        for value in 1..size {
            left = concatenate_sequence_terms(left, singleton(value as u32));
        }
        let right = SequenceTerm {
            element_type: Some(CType::Int32),
            node: std::sync::Arc::new(SequenceTermNode::Literal(
                (0..size)
                    .map(|n| int32(n as u32))
                    .collect::<Vec<_>>()
                    .into(),
            )),
        };
        let equality = finite_sequence_equality(&left, &right);
        let mut pending = vec![(&equality, 0)];
        let mut nodes = 0;
        let mut depth = 0;
        while let Some((proposition, current_depth)) = pending.pop() {
            nodes += 1;
            depth = depth.max(current_depth);
            if let Proposition::And(left, right) = proposition {
                pending.push((left, current_depth + 1));
                pending.push((right, current_depth + 1));
            }
        }
        assert_eq!(nodes, 2 * size - 1);
        assert_eq!(depth, size.ilog2());
    }
}

#[test]
fn repeated_concatenation_shares_the_existing_root() {
    for size in [8usize, 64, 512] {
        let mut sequence = singleton(0);
        for value in 1..size {
            let previous_root = sequence.node.clone();
            sequence = concatenate_sequence_terms(sequence, singleton(value as u32));
            let SequenceTermNode::Concat(left, _) = sequence.node.as_ref() else {
                panic!("nonempty concatenation should retain a rope node");
            };
            assert!(
                std::sync::Arc::ptr_eq(&left.node, &previous_root),
                "concatenating size {value} copied the existing sequence"
            );
        }
    }
}

#[test]
fn empty_concatenation_reuses_the_nonempty_root() {
    let empty = SequenceTerm {
        element_type: None,
        node: std::sync::Arc::new(SequenceTermNode::Literal(Vec::new().into())),
    };
    let value = singleton(7);
    let root = value.node.clone();

    assert!(std::sync::Arc::ptr_eq(
        &concatenate_sequence_terms(empty.clone(), value.clone()).node,
        &root,
    ));
    assert!(std::sync::Arc::ptr_eq(
        &concatenate_sequence_terms(value, empty).node,
        &root,
    ));
}
