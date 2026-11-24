//! Mixed call carriers retain expression roots and their exact argument forms.
use super::*;

#[test]
fn mixed_call_arguments_import_structurally_and_keep_exact_native_forms() {
    let _session = crate::kernel::VerificationSession::enter();
    let ty = TypeParameterName::intern("MixedArgumentT").algebraic_type();
    let algebraic = AlgebraicTerm {
        algebraic_type: ty.clone(),
        node: AlgebraicTermNode::PureFunctionApplication {
            name: "abstract_seed".into(),
            arguments: vec![PureFunctionArgument::Integer(
                IntegerTerm::Variable(Variable(1008500)).into(),
            )],
        },
    };
    let pointer = Pointer::new(
        Address::symbolic(Variable(1008501)),
        ProgramType::Int32Pointer,
    );
    let arguments = vec![
        PureFunctionArgument::Algebraic(algebraic.clone()),
        PureFunctionArgument::Value(ProgramValue::Parameter(Box::new(algebraic))),
        PureFunctionArgument::Value(ProgramValue::Pointer(pointer.clone())),
        PureFunctionArgument::ArrayRef {
            point: crate::kernel::ProgramPoint::of_memory(&SymbolicMemory::new()),
            pointer: ProgramValue::Pointer(pointer),
            element_type: ProgramType::Int32,
        },
        PureFunctionArgument::Value(ProgramValue::Bool(MachineTerm::Constant {
            format: MachineIntegerType::UInt8,
            bits: 1,
        })),
        PureFunctionArgument::Value(ProgramValue::Bool(MachineTerm::Variable(Variable(1008505)))),
        PureFunctionArgument::Value(ProgramValue::Bool(MachineTerm::bool_cast(
            MachineIntegerType::UInt8,
            ConditionTerm::bool_application("mixed_bool", vec![]),
        ))),
        PureFunctionArgument::Value(ProgramValue::Float64(
            MachineTerm::ClickFunctionApplication {
                name: "mixed_float".into(),
                arguments: vec![PureFunctionArgument::Value(ProgramValue::Float32(
                    MachineTerm::uint32_constant(0x7fc00123),
                ))],
            },
        )),
    ];
    let mut import = KernelTermImport::default();
    let roots = arguments
        .iter()
        .map(|arg| import.argument(arg))
        .collect::<Vec<_>>();
    assert!(
        roots
            .iter()
            .all(|root| !root.requires_native_argument_input())
    );
    assert_ne!(
        roots[0], roots[1],
        "logical and program algebraic argument forms differ"
    );
    for (root, expected) in roots.iter().zip(&arguments) {
        let actual = KernelTermExport::default().argument(root).unwrap();
        assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
    }
    let application = SharedPureApplication::intern("mixed_result".into(), arguments.clone());
    let integer = import.integer(&IntegerTerm::PureFunctionApplication(application.clone()).into());
    let machine = import.machine_call(MachineIntegerType::Int32, &application);
    let boolean = import.boolean_call(&application);
    for call in [&integer, &machine, &boolean] {
        assert!(
            call.children()
                .iter()
                .all(|root| !root.requires_native_argument_input())
        );
    }
    assert_eq!(
        format!(
            "{:?}",
            KernelTermExport::default()
                .integer(&integer)
                .unwrap()
                .as_ref()
        ),
        format!(
            "{:?}",
            IntegerTerm::PureFunctionApplication(application.clone())
        )
    );
    assert_eq!(
        format!("{:?}", machine.machine_conversion_leaf().unwrap()),
        format!(
            "{:?}",
            MachineTerm::ClickFunctionApplication {
                name: "mixed_result".into(),
                arguments: arguments.clone()
            }
        )
    );
    assert_eq!(
        format!("{:?}", KernelTermExport::condition(&boolean).unwrap()),
        format!("{:?}", ConditionTerm::BoolApplication(application))
    );
    let float = KernelTerm::float_call(
        KernelFloatType::Float64,
        "mixed_result".into(),
        roots.into_iter().map(|root| (root, None)).collect(),
    );
    assert_eq!(
        format!("{:?}", KernelTermExport::float(&float).unwrap()),
        format!(
            "{:?}",
            ProgramValue::Float64(MachineTerm::ClickFunctionApplication {
                name: "mixed_result".into(),
                arguments
            })
        )
    );
}

#[test]
fn noncanonical_boolean_carriers_keep_exact_native_payloads() {
    let _session = crate::kernel::VerificationSession::enter();
    for word in [
        MachineTerm::Constant {
            format: MachineIntegerType::UInt8,
            bits: 2,
        },
        MachineTerm::BoolCast {
            to: MachineIntegerType::UInt16,
            value: Box::new(ConditionTerm::Variable(Variable(1008506))),
        },
        MachineTerm::BoolCast {
            to: MachineIntegerType::UInt8,
            value: Box::new(ConditionTerm::Constant(true)),
        },
    ] {
        let source = PureFunctionArgument::Value(ProgramValue::Bool(word));
        let root = KernelTermImport::default().argument(&source);
        assert_eq!(
            format!("{:?}", KernelTermExport::default().argument(&root).unwrap()),
            format!("{source:?}")
        );
    }
}

#[test]
fn prepared_call_children_reuse_the_producer_only_in_the_current_session() {
    let application = SharedPureApplication::intern(
        "session_pointer_argument".into(),
        vec![PureFunctionArgument::Value(ProgramValue::Pointer(
            Pointer::new(
                Address::symbolic(Variable(1008515)),
                ProgramType::Int32Pointer,
            ),
        ))],
    );
    let first = {
        let _session = crate::kernel::VerificationSession::enter();
        let first = application.common_argument(0).unwrap();
        assert_eq!(application.common_argument(0).as_ref(), Some(&first));
        first
    };
    let _session = crate::kernel::VerificationSession::enter();
    let second = application.common_argument(0).unwrap();
    assert_ne!(
        first, second,
        "fresh sessions must prepare their own pointer payloads"
    );
    assert!(
        first
            .pointer_payload()
            .unwrap()
            .same_source_payload(second.pointer_payload().unwrap())
    );
}

#[test]
fn prepared_call_children_do_not_cross_threads_with_equal_session_generations() {
    let _session = crate::kernel::VerificationSession::enter();
    let application = SharedPureApplication::intern(
        "thread_pointer_argument".into(),
        vec![PureFunctionArgument::Value(ProgramValue::Pointer(
            Pointer::new(
                Address::symbolic(Variable(1008517)),
                ProgramType::Int32Pointer,
            ),
        ))],
    );
    let first = application.common_argument(0).unwrap();
    let generation = crate::kernel::verification_session_generation();
    let other = std::thread::spawn(move || {
        for _ in 1..generation {
            let _session = crate::kernel::VerificationSession::enter();
        }
        let _session = crate::kernel::VerificationSession::enter();
        assert_eq!(crate::kernel::verification_session_generation(), generation);
        application.common_argument(0).unwrap()
    })
    .join()
    .unwrap();
    assert_ne!(first, other);
    assert!(
        first
            .pointer_payload()
            .unwrap()
            .same_source_payload(other.pointer_payload().unwrap())
    );
}

#[test]
fn opaque_call_children_borrow_their_producers_exact_argument_slot() {
    let _session = crate::kernel::VerificationSession::enter();
    let argument = PureFunctionArgument::Value(ProgramValue::Bool(MachineTerm::Constant {
        format: MachineIntegerType::UInt8,
        bits: 2,
    }));
    let name = "opaque_boolean_argument".to_string();
    let first = SharedPureApplication::intern(name.clone(), vec![argument.clone()]);
    let second = SharedPureApplication::intern(name, vec![argument.clone()]);
    assert_eq!(first, second);
    assert_ne!(first.payload_id(), second.payload_id());
    let mut import = KernelTermImport::default();
    assert!(first.common_argument(0).is_none());

    let machine = import.machine_call(MachineIntegerType::Int32, &first);
    let boolean = import.boolean_call(&first);
    let integer = import.integer(&IntegerTerm::PureFunctionApplication(first.clone()).into());
    let pointer = SharedPointer::import(&Pointer::new(
        Address::symbolic(Variable(1008520)),
        ProgramType::Int32Pointer,
    ));
    let pointer = import.pointer_call(&first, vec![None], pointer);
    let KernelTermNode::PointerCall {
        call: pointer_call, ..
    } = pointer.node()
    else {
        panic!("pointer call");
    };
    for call in [&machine, &boolean, &integer, pointer_call] {
        let [child] = call.children() else {
            panic!("one exact argument");
        };
        assert!(matches!(child.node(), KernelTermNode::ImportedScalar(_)));
        assert!(std::ptr::eq(
            child.written_argument().unwrap(),
            &first.arguments()[0],
        ));
        assert_eq!(
            KernelTermExport::default().argument(child).unwrap(),
            argument
        );
    }

    let other = import.machine_call(MachineIntegerType::Int32, &second);
    assert_ne!(machine.children(), other.children());
    let other = import.integer(&IntegerTerm::PureFunctionApplication(second.clone()).into());
    assert_ne!(integer.children(), other.children());
    let [child] = other.children() else {
        panic!("one exact argument");
    };
    assert!(matches!(child.node(), KernelTermNode::ImportedScalar(_)));
    assert!(std::ptr::eq(
        child.written_argument().unwrap(),
        &second.arguments()[0],
    ));
    assert_eq!(
        KernelTermExport::default().integer(&integer).unwrap(),
        KernelTermExport::default().integer(&other).unwrap()
    );
}

/// A null array views no memory, so a null array argument formed at
/// different states is one term, while a non-null one keeps its states apart.
#[test]
fn a_null_array_argument_is_formed_at_no_state() {
    let _session = crate::kernel::VerificationSession::enter();
    let empty = crate::kernel::ProgramPoint::of_memory(&SymbolicMemory::new());
    let other =
        crate::kernel::ProgramPoint::of_memory(&SymbolicMemory::new().with_block("local:x", 8));
    let pointer = |address: Address| {
        KernelTerm::shared_pointer_value(SharedPointer::import(&Pointer::new(
            address,
            ProgramType::Int32Pointer,
        )))
    };
    let array = |point: &crate::kernel::ProgramPoint, pointer: &KernelTerm| {
        KernelTerm::shared_array_reference(point.clone(), pointer.clone(), ProgramType::Int32)
    };
    let null = pointer(Address::null());
    assert_eq!(array(&empty, &null), array(&other, &null));
    let symbolic = pointer(Address::symbolic(Variable(1008601)));
    assert_ne!(array(&empty, &symbolic), array(&other, &symbolic));
}

#[test]
fn opaque_call_observation_borrows_the_written_argument_slot() {
    let _session = crate::kernel::VerificationSession::enter();
    let native = PureFunctionArgument::Value(ProgramValue::Bool(MachineTerm::Constant {
        format: MachineIntegerType::UInt8,
        bits: 2,
    }));
    let build = || {
        let producer =
            SharedPureApplication::intern("opaque_bool_input".into(), vec![native.clone()]);
        let call = KernelTermImport::default().machine_call(MachineIntegerType::Int32, &producer);
        let child = call.children()[0].clone();
        assert!(std::ptr::eq(
            child.written_argument().unwrap(),
            &producer.arguments()[0],
        ));
        child
    };
    let first = build();
    let second = build();
    assert_ne!(first, second);
    let observe = |term: &KernelTerm| {
        let KernelTermNode::ImportedScalar(input) = term.node() else {
            panic!("expected a typed scalar input");
        };
        assert_eq!(input.carrier(), ProgramType::Bool);
        term.observe_imported_scalar(input)
    };
    let key = observe(&first);
    assert!(std::ptr::eq(
        key.written_argument().unwrap(),
        first.written_argument().unwrap(),
    ));
    assert_eq!(key, observe(&second));
    let direct = KernelTermImport::default().argument(&native);
    assert_ne!(direct, first);
    assert_eq!(observe(&direct), key);
    assert_eq!(KernelTermExport::default().argument(&key).unwrap(), native);
    for root in [first, second, direct, key] {
        assert!(!root.has_cached_native_argument());
    }
}
