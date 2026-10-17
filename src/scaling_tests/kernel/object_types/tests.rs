use super::*;

#[test]
fn hashing_a_pointer_word_does_not_walk_its_type_origins() {
    #[derive(Default)]
    struct ByteCounter(usize);
    impl std::hash::Hasher for ByteCounter {
        fn finish(&self) -> u64 {
            self.0 as u64
        }
        fn write(&mut self, bytes: &[u8]) {
            self.0 += bytes.len();
        }
    }
    let mut samples = Vec::new();
    for count in [16, 64, 256, 1024] {
        let mut evidence = ObjectTypeEvidence::from(class());
        let mut reversed = ObjectTypeEvidence::from(class());
        for index in 0..count {
            evidence = evidence.merge(&ObjectTypeEvidence::parameter(class(), index, 77, true));
            reversed = reversed.merge(&ObjectTypeEvidence::parameter(class(), count - index - 1, 77, true));
        }
        assert_eq!(evidence, reversed);
        let word = crate::kernel::eval::cast_c_value_to_type(
            CValue::typed_pointer(Pointer::symbolic(Variable(930_444)), CType::Int32Pointer)
                .with_pointer_object_type_evidence(Some(evidence)),
            CType::UInt64, crate::kernel::eval::IntegerConversion::Modular,
            &mut Vec::new(), &PureFactContext::new(),
        ).unwrap();
        let mut counter = ByteCounter::default();
        std::hash::Hash::hash(&word, &mut counter);
        samples.push(counter.0);
    }
    assert!(samples[0] > 0);
    assert!(
        samples.iter().all(|sample| *sample == samples[0]),
        "{samples:?}"
    );
}

