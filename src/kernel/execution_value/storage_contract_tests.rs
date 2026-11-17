use super::*;
use crate::kernel::VerificationSession;
use std::hash::{Hash, Hasher};

fn hash(value: &impl Hash) -> u64 {
    let mut state = std::collections::hash_map::DefaultHasher::new();
    value.hash(&mut state);
    state.finish()
}

fn retained(value: &ProgramValue) -> StoredExecutionValue {
    let root = KernelTermImport::default().argument(&PureFunctionArgument::Value(value.clone()));
    ExecutionValue::Shared(root).into()
}

#[test]
fn nonnumeric_storage_keys_preserve_native_pairwise_order_and_hash_classes() {
    let _session = VerificationSession::enter();
    let mut values = vec![ProgramValue::Void];
    for word in [
        MachineTerm::Constant {
            format: MachineIntegerType::UInt8,
            bits: 2,
        },
        MachineTerm::Variable(Variable(998601)),
        MachineTerm::bool_cast(
            MachineIntegerType::UInt8,
            ConditionTerm::Variable(Variable(998602)),
        ),
    ] {
        values.push(ProgramValue::Bool(word));
    }
    for bits in [0, 0x80000000, 0x7fc00001, 0x7fc00002] {
        values.push(ProgramValue::Float32(MachineTerm::uint32_constant(bits)));
    }
    for bits in [0, 0x8000000000000000, 0x7ff8000000000001] {
        values.push(ProgramValue::Float64(MachineTerm::uint64_constant(bits)));
    }
    values.push(ProgramValue::Pointer(PointerValue::new(
        Pointer::symbolic(Variable(998603)),
        ProgramType::Int32Pointer,
    )));
    for left in &values {
        for right in &values {
            let expected = left.cmp(right);
            for a in [StoredExecutionValue::from(left.clone()), retained(left)] {
                for b in [StoredExecutionValue::from(right.clone()), retained(right)] {
                    assert_eq!(a.cmp(&b), expected, "{left:?} vs {right:?}");
                    assert_eq!(a == b, left == right);
                    if a == b {
                        assert_eq!(hash(&a), hash(&b));
                    }
                }
            }
            let a = StoredMemoryValue::from(left.clone());
            let b = StoredMemoryValue::from(right.clone());
            assert_eq!(a.cmp(&b), expected);
            assert_eq!(
                hash(&a),
                hash(left),
                "memory hashes preserve native streams"
            );
        }
    }
}

#[test]
fn float_storage_preserves_exact_call_argument_carrier_distinctions() {
    let _session = VerificationSession::enter();
    let word = MachineTerm::Variable(Variable(998610));
    let arguments = [
        PureFunctionArgument::Value(ProgramValue::UInt32(word.clone())),
        PureFunctionArgument::SharedMachine(SharedMachineIntegerTerm::intern(
            MachineIntegerType::UInt32,
            word,
        )),
    ];
    let values = arguments.map(|argument| {
        ProgramValue::Float32(MachineTerm::ClickFunctionApplication {
            name: "storage_contract".into(),
            arguments: vec![argument],
        })
    });
    assert_ne!(values[0], values[1]);
    for a in &values {
        for b in &values {
            let left = retained(a);
            let right = retained(b);
            assert_eq!(left == right, a == b);
            assert_eq!(left.cmp(&right), a.cmp(b));
            assert_eq!(left.same_native_value(&right), a == b);
        }
    }
}
