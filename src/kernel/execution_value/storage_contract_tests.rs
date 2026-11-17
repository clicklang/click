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

#[test]
fn boolean_connective_keys_keep_native_condition_identity_and_order() {
    let _session = VerificationSession::enter();
    let a = ConditionTerm::Variable(Variable(998670));
    let b = ConditionTerm::Variable(Variable(998671));
    let cases = [
        ConditionTerm::Constant(false),
        a.clone(),
        ConditionTerm::BoolEqual(Box::new(a.clone()), Box::new(b.clone())),
        ConditionTerm::BoolIf {
            condition: Box::new(a.clone()),
            then_condition: Box::new(b.clone()),
            else_condition: Box::new(a.clone()),
        },
        ConditionTerm::BoolApplication(SharedPureApplication::intern("key_bool".into(), vec![])),
    ];
    let roots = cases
        .iter()
        .map(|term| KernelTermImport::default().condition(term))
        .collect::<Vec<_>>();
    let native = roots
        .iter()
        .map(|root| ExecutionValue::Shared(root.clone()).into_native())
        .collect::<Vec<_>>();
    for (i, a) in roots.iter().enumerate() {
        for (j, b) in roots.iter().enumerate() {
            let left = StoredExecutionValue::from(ExecutionValue::Shared(a.clone()));
            let right = StoredExecutionValue::from(ExecutionValue::Shared(b.clone()));
            assert_eq!(left.cmp(&right), native[i].cmp(&native[j]));
            assert_eq!(left == right, native[i] == native[j]);
            let legacy = StoredExecutionValue::from(native[i].clone());
            assert_eq!(left, legacy);
            assert_eq!(hash(&left), hash(&legacy));
        }
    }
}

#[test]
fn deep_boolean_key_construction_and_drop_use_a_small_stack() {
    std::thread::Builder::new()
        .stack_size(256 << 10)
        .spawn(|| {
            let _session = VerificationSession::enter();
            let atom = KernelTerm::variable(KernelType::Bool, Variable(998675));
            let other = KernelTerm::variable(KernelType::Bool, Variable(998676));
            let mut root = atom.clone();
            for _ in 0..4096 {
                root = KernelTerm::boolean_if_raw([atom.clone(), root, other.clone()]);
            }
            let value = StoredExecutionValue::from(ExecutionValue::Shared(root.clone()));
            assert!(!root.has_cached_native_argument());
            let _ = hash(&value);
            assert!(!root.has_cached_native_argument());
            drop(root);
            drop(value);
        })
        .unwrap()
        .join()
        .unwrap();
}
