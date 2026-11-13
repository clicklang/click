use super::*;

#[test]
fn machine_call_roots_preserve_types_arguments_and_native_roundtrips() {
    let _session = crate::kernel::VerificationSession::enter();
    let input = KernelTerm::variable(KernelType::C(CType::UInt32), Variable(995800));
    let native = SharedPureApplication::intern(
        "f".into(),
        vec![PureFunctionArgument::Value(CValue::UInt32(
            MachineTerm::Variable(Variable(995800)),
        ))],
    );
    let retained = SharedPureApplication::intern(
        "f".into(),
        vec![PureFunctionArgument::SharedMachine(
            SharedMachineIntegerTerm::from_shared(MachineIntegerType::UInt32, input.clone())
                .unwrap(),
        )],
    );
    let mut roots = Vec::new();
    for format in [
        MachineIntegerType::Int8,
        MachineIntegerType::UInt8,
        MachineIntegerType::Int16,
        MachineIntegerType::UInt16,
        MachineIntegerType::Int32,
        MachineIntegerType::UInt32,
        MachineIntegerType::Int64,
        MachineIntegerType::UInt64,
        MachineIntegerType::Int128,
        MachineIntegerType::UInt128,
    ] {
        let exports = KernelTermExport::machine_export_count();
        let root = KernelTermImport::default().machine_call(format, &native);
        assert_eq!(
            root,
            KernelTermImport::default().machine_call(format, &retained)
        );
        assert_eq!(root.ty(), &KernelType::C(format.c_type()));
        assert_eq!(root.children(), &[input.clone()]);
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert_eq!(
            KernelTermExport::machine(&root).unwrap(),
            MachineTerm::ClickFunctionApplication {
                name: "f".into(),
                arguments: native.arguments().to_vec()
            }
        );
        assert!(
            !root.is_shared_machine_operand(),
            "consumer admission is a later slice"
        );
        roots.push(root);
    }
    for (i, a) in roots.iter().enumerate() {
        for b in &roots[i + 1..] {
            assert_ne!(a, b);
        }
    }
    let other = SharedPureApplication::intern("g".into(), native.arguments().to_vec());
    assert_ne!(
        roots[4],
        KernelTermImport::default().machine_call(MachineIntegerType::Int32, &other)
    );
}

#[test]
fn machine_call_roots_preserve_opaque_producer_payloads() {
    let _session = crate::kernel::VerificationSession::enter();
    let pointer = CPointerValue::new(Pointer::symbolic(Variable(995801)), CType::VoidPointer);
    let application = SharedPureApplication::intern(
        "pointer_arg".into(),
        vec![PureFunctionArgument::Value(CValue::Pointer(
            pointer.clone(),
        ))],
    );
    let format = MachineIntegerType::Int32;
    let root = KernelTermImport::default().machine_call(format, &application);
    assert_eq!(
        root,
        KernelTermImport::default().machine_call(format, &application)
    );
    let class = crate::kernel::effective_type::CAccessClass::Scalar(
        crate::kernel::effective_type::CScalarClass::Long,
    );
    let second = SharedPureApplication::intern(
        application.name().into(),
        vec![PureFunctionArgument::Value(CValue::Pointer(
            pointer
                .clone()
                .with_declared_object_class(Some(class.clone())),
        ))],
    );
    assert_eq!(application, second, "semantic identity");
    assert_ne!(
        root,
        KernelTermImport::default().machine_call(format, &second),
        "distinct exact producer payloads"
    );
    let second_root = KernelTermImport::default().machine_call(format, &second);
    for (call, expected) in [(&root, None), (&second_root, Some(class))] {
        let MachineTerm::ClickFunctionApplication { arguments, .. } =
            KernelTermExport::machine(call).unwrap()
        else {
            panic!()
        };
        let PureFunctionArgument::Value(CValue::Pointer(pointer)) = &arguments[0] else {
            panic!()
        };
        assert_eq!(pointer.object_class(), expected);
    }
    drop(application);
    let MachineTerm::ClickFunctionApplication { arguments, .. } =
        KernelTermExport::machine(&root).unwrap()
    else {
        panic!()
    };
    assert_eq!(
        arguments,
        vec![PureFunctionArgument::Value(CValue::Pointer(pointer))]
    );
}

#[test]
fn machine_call_argument_order_and_read_snapshots_remain_distinct() {
    let _session = crate::kernel::VerificationSession::enter();
    let pointer = Pointer::symbolic(Variable(995802));
    let before = crate::kernel::intern_c_memory(CMemory::new());
    let after = crate::kernel::intern_c_memory(
        CMemory::new().store(pointer.clone(), CValue::Int32(7u32.into())),
    );
    let calls = [before, after].map(|memory| {
        SharedPureApplication::intern(
            "read_arg".into(),
            vec![PureFunctionArgument::Value(CValue::Int32(
                MachineTerm::MemoryLoad(memory, Box::new(pointer.clone()), LoadKind::Int32),
            ))],
        )
    });
    let roots = calls
        .map(|call| KernelTermImport::default().machine_call(MachineIntegerType::Int32, &call));
    assert_ne!(roots[0], roots[1]);
    let args = [1u32, 2].map(|x| PureFunctionArgument::Value(CValue::Int32(x.into())));
    let a = SharedPureApplication::intern("ordered".into(), args.to_vec());
    let b = SharedPureApplication::intern("ordered".into(), args.into_iter().rev().collect());
    assert_ne!(
        KernelTermImport::default().machine_call(MachineIntegerType::Int32, &a),
        KernelTermImport::default().machine_call(MachineIntegerType::Int32, &b)
    );
}

mod scaling_tests {
    include!("../../../scaling_tests/kernel/primitives/kernel_term_machine_calls.rs");
}
