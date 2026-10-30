//! Congruence signatures, not function evaluation or predicate search.
//! Curried application nodes have shallow keys and indexed parent uses. A late
//! operand merge therefore updates precisely the applications depending on it.
use super::*;
use crate::kernel::MachineBinaryOp;
use crate::kernel::MachineIntegerType;
use crate::kernel::machine_integer::representation;
use crate::kernel::{
    Bitvector32Term as T, BitvectorUnaryOp as U, CType, CValue, CarrierWidth as W,
    ConditionTerm as C, PureFunctionArgument as A, SharedPureApplication,
};
use crate::kernel::{CompareRelation, OverflowOperation};
use crate::kernel::{binary_term, unary_term};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum ArgumentTag {
    Value(CType),
    Array((u32, u32), CType),
    Algebraic,
    DesignationRead((u32, u32)),
    PointerExtentRead((u32, u32)),
    PointerRootExtent,
    PointerSubobjectExtent,
    PointerCallDesignation,
    PointerCallExtent,
    Integer,
}

/// The head an interned call gets: a pointer function's value, its
/// identity, or a `-> Bool` function's application.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::kernel::equality_graph) enum CallHead {
    Pointer,
    PointerIdentity,
    Bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(in crate::kernel::equality_graph) enum ConditionKind {
    Int32Eq,
    Int32Lt,
    Int32Le,
    Int32Gt,
    Int32Ge,
    Int32AddOverflow,
    UInt64Eq,
    Int64Lt,
    Int64Le,
    Int64Gt,
    Int64Ge,
    UInt64Lt,
    UInt64Le,
    UInt64Gt,
    UInt64Ge,
    PointerEq,
    PointerValueEq,
    OffsetEq,
    AlgebraicEq,
    IntegerEq,
    IntegerNe,
    IntegerLt,
    IntegerLe,
    IntegerGt,
    IntegerGe,
    UInt32Lt,
    UInt32Le,
    UInt32Gt,
    UInt32Ge,
    /// The logical equality of two `Bool` values (rule L-Eq).
    BoolEq,
    /// A fact about a `Bool` value that is not a comparison: an
    /// application, a conditional or a read. Its truth is the annotation of
    /// the value's class, which can also arrive through an L-Eq merge.
    BoolValue,
}

/// Shared classification for registration and the opaque-atom lookup fast path.
/// An expression with indexed operands must never be queried as an opaque atom.
pub(in crate::kernel::equality_graph) fn has_machine_operands(term: &T) -> bool {
    term.as_binary().is_some_and(|(op, _, _)| !op.is_float())
        || term
            .as_unary()
            .is_some_and(|(op, _)| !matches!(op, U::Float32Negate | U::Float64Negate))
        || matches!(
            term,
            T::ClickFunctionApplication { .. } | T::IntegerToMachine { .. } | T::MemoryLoad(..)
        )
        || matches!(term, T::Variable(variable) if crate::kernel::is_load_variable(variable))
}

impl TermClasses {
    /// Walk mixed-width machine applications once. In particular, a nested
    /// pure call does not recursively canonicalize every enclosing subtree.
    pub(super) fn intern_machine(&mut self, term: &T, wide: bool) -> u64 {
        self.intern_typed_machine(term, if wide { W::Bits64 } else { W::Bits32 })
    }

    fn intern_typed_machine(&mut self, term: &T, width: W) -> u64 {
        self.intern_expression(Some((term, width)), None, None, None, None)
    }

    pub(super) fn intern_algebraic(&mut self, term: &crate::kernel::AlgebraicTerm) -> u64 {
        self.intern_expression(None, Some(term), None, None, None)
    }

    pub(super) fn intern_integer(&mut self, term: &crate::kernel::IntegerTerm) -> u64 {
        self.intern_expression(None, None, Some(term), None, None)
    }

    pub(in crate::kernel::equality_graph) fn add_integer_equality(
        &mut self,
        left: &crate::kernel::IntegerTerm,
        right: &crate::kernel::IntegerTerm,
    ) -> bool {
        let a = self.intern_integer(left);
        let b = self.intern_integer(right);
        self.register_pending_loads();
        self.close(vec![(a, b)])
    }

    pub(in crate::kernel::equality_graph) fn are_integer_equal(
        &mut self,
        left: &crate::kernel::IntegerTerm,
        right: &crate::kernel::IntegerTerm,
    ) -> bool {
        let a = self.intern_integer(left);
        let b = self.intern_integer(right);
        self.register_pending_loads();
        self.root(a) == self.root(b)
    }

    pub(super) fn intern_pointer_call(&mut self, application: &SharedPureApplication) -> u64 {
        self.intern_expression(
            None,
            None,
            None,
            None,
            Some((application, CallHead::Pointer)),
        )
    }

    pub(super) fn intern_pointer_call_identity(
        &mut self,
        application: &SharedPureApplication,
    ) -> u64 {
        self.intern_expression(
            None,
            None,
            None,
            None,
            Some((application, CallHead::PointerIdentity)),
        )
    }

    /// The class of a `-> Bool` pure function's application: its head and
    /// argument classes, so applications to equal arguments are congruent.
    pub(super) fn intern_bool_call(&mut self, application: &SharedPureApplication) -> u64 {
        self.intern_expression(None, None, None, None, Some((application, CallHead::Bool)))
    }

    fn intern_expression(
        &mut self,
        machine: Option<(&T, W)>,
        algebraic: Option<&crate::kernel::AlgebraicTerm>,
        integer: Option<&crate::kernel::IntegerTerm>,
        value: Option<&CValue>,
        pointer_call: Option<(&SharedPureApplication, CallHead)>,
    ) -> u64 {
        enum Binary {
            Int32Add,
            Int32(Int32Binary),
            UInt64(UInt64Binary),
        }
        enum Work<'a> {
            PointerCall(&'a SharedPureApplication, CallHead),
            Algebraic(&'a crate::kernel::AlgebraicTerm),
            Integer(&'a crate::kernel::IntegerTerm),
            RememberInteger(crate::kernel::SharedIntegerTerm),
            Field(&'a crate::kernel::AlgebraicValue),
            Machine(&'a T, W),
            OpaqueCount(&'a T),
            Argument(&'a A),
            Value(&'a CValue),
            Wrap(ArgumentTag),
            Call(u64, usize),
            Binary(Binary),
            Unary(Int32Unary, bool),
            /// A conversion into an 8- or 16-bit format, whose operand's
            /// class is on the value stack: the cast node, joined with its
            /// rule-K7 word.
            NarrowCast {
                source: MachineIntegerType,
                destination: MachineIntegerType,
                inverse: bool,
            },
        }
        let mut pending = if let Some(value) = value {
            vec![Work::Value(value)]
        } else if let Some((term, width)) = machine {
            vec![Work::Machine(term, width)]
        } else if let Some(term) = integer {
            vec![Work::Integer(term)]
        } else if let Some((call, identity)) = pointer_call {
            vec![Work::PointerCall(call, identity)]
        } else {
            vec![Work::Algebraic(algebraic.expect("expression"))]
        };
        // Shared Integer children form a DAG: process each selected node once,
        // including when a source uses the same large child twice.
        let mut integer_values = std::collections::BTreeMap::new();
        let mut values = Vec::new();
        while let Some(work) = pending.pop() {
            // Preserve existing scalar work accounting; new argument/call
            // nodes are charged once each, like the old wide traversal.
            if !matches!(
                &work,
                Work::Machine(_, W::Bits32) | Work::Binary(Binary::Int32Add | Binary::Int32(_))
            ) {
                crate::instrumentation::record_deterministic_work(1);
            }
            let scalar_source = match &work {
                Work::Machine(term, W::Bits32) if matches!(term, T::If { .. }) => Some(*term),
                _ => None,
            };
            let node = match work {
                Work::PointerCall(application, identity) => {
                    let symbol =
                        SharedPureApplication::intern(application.name().to_owned(), vec![]);
                    let arity = application.arguments().len();
                    let head = self.intern_node(match identity {
                        CallHead::PointerIdentity => Node::PointerFunctionValue(symbol, arity),
                        CallHead::Pointer => Node::PointerFunction(symbol, arity),
                        CallHead::Bool => Node::BoolFunction(symbol, arity),
                    });
                    pending.push(Work::Call(head, application.arguments().len()));
                    pending.extend(application.arguments().iter().rev().map(Work::Argument));
                    continue;
                }
                Work::OpaqueCount(term) => {
                    values.push(self.opaque_argument(&A::Value(CValue::UInt64(term.clone()))));
                    continue;
                }
                Work::RememberInteger(term) => {
                    integer_values.insert(term, *values.last().expect("Integer value"));
                    continue;
                }
                Work::Integer(term) => {
                    use crate::kernel::IntegerTerm as I;
                    let shared = crate::kernel::SharedIntegerTerm::intern(term.clone());
                    if let Some(value) = integer_values.get(&shared) {
                        values.push(*value);
                        continue;
                    }
                    pending.push(Work::RememberInteger(shared.clone()));
                    let binary = match term {
                        I::Add(a, b) => Some((IntegerOperation::Add, a, b)),
                        I::Subtract(a, b) => Some((IntegerOperation::Subtract, a, b)),
                        I::Multiply(a, b) => Some((IntegerOperation::Multiply, a, b)),
                        I::TruncatingQuotient(a, b) => Some((IntegerOperation::Quotient, a, b)),
                        I::TruncatingRemainder(a, b) => Some((IntegerOperation::Remainder, a, b)),
                        _ => None,
                    };
                    if let Some((op, a, b)) = binary {
                        let head = self.intern_node(Node::IntegerOperation(op));
                        pending.push(Work::Call(head, 2));
                        pending.push(Work::Integer(b));
                        pending.push(Work::Integer(a));
                        continue;
                    }
                    match term {
                        I::Constant(value) => {
                            use crate::kernel::{MachineIntegerConstant, MachineIntegerType as M};
                            let literal = self.intern_node(Node::IntegerAtom(shared));
                            // Literal observations are folded by Integer constructors.
                            // Install their bounded typed spellings so a late machine
                            // equality reaches that same canonical Integer literal.
                            for ty in [
                                M::Int8,
                                M::UInt8,
                                M::Int16,
                                M::UInt16,
                                M::Int32,
                                M::UInt32,
                                M::Int64,
                                M::UInt64,
                                M::Int128,
                                M::UInt128,
                            ] {
                                let Some(bits) =
                                    MachineIntegerConstant::from_integer(ty.format(), value)
                                        .and_then(|constant| ty.constant_term(constant))
                                else {
                                    continue;
                                };
                                let operand =
                                    self.intern_typed_machine(&bits, W::of_machine_type(ty));
                                let head = self.intern_node(Node::IntegerOperation(
                                    IntegerOperation::Observe(ty),
                                ));
                                let observed = self.intern_node(Node::Apply(head, operand));
                                self.close(vec![(literal, observed)]);
                            }
                            values.push(literal);
                            continue;
                        }
                        I::Machine(value) => {
                            let head = self.intern_node(Node::IntegerOperation(
                                IntegerOperation::Observe(value.ty()),
                            ));
                            pending.push(Work::Call(head, 1));
                            pending
                                .push(Work::Machine(value.value(), W::of_machine_type(value.ty())));
                            continue;
                        }
                        I::Negate(value) => {
                            let head =
                                self.intern_node(Node::IntegerOperation(IntegerOperation::Negate));
                            pending.push(Work::Call(head, 1));
                            pending.push(Work::Integer(value));
                            continue;
                        }
                        I::PureFunctionApplication(application) => {
                            let symbol = SharedPureApplication::intern(
                                application.name().to_owned(),
                                vec![],
                            );
                            let head = self.intern_node(Node::IntegerFunction(
                                symbol,
                                application.arguments().len(),
                            ));
                            pending.push(Work::Call(head, application.arguments().len()));
                            pending
                                .extend(application.arguments().iter().rev().map(Work::Argument));
                            continue;
                        }
                        // Binder-bearing match/fold terms retain their complete,
                        // shallow interned identity.
                        _ => Node::IntegerAtom(shared),
                    }
                }
                Work::Algebraic(term) => {
                    use crate::kernel::AlgebraicTermNode as N;
                    let ty = self.algebraic_type_token(&term.algebraic_type);
                    match &term.node {
                        N::Variable(variable) => Node::AlgebraicVariable(ty, *variable),
                        N::Constructor { variant, fields } => {
                            let head = self.intern_node(Node::AlgebraicConstructor(
                                ty,
                                variant.clone(),
                                fields.len(),
                            ));
                            pending.push(Work::Call(head, fields.len()));
                            pending.extend(fields.iter().rev().map(Work::Field));
                            continue;
                        }
                        N::PureFunctionApplication { name, arguments } => {
                            let head = self.intern_node(Node::AlgebraicFunction(
                                ty,
                                name.clone(),
                                arguments.len(),
                            ));
                            pending.push(Work::Call(head, arguments.len()));
                            pending.extend(arguments.iter().rev().map(Work::Argument));
                            continue;
                        }
                        N::MemoryLoad { memory, pointer } => {
                            let head = self.intern_node(Node::AlgebraicMemoryRead(
                                ty.clone(),
                                memory.read_identity(),
                            ));
                            let address = self.numeric_address(pointer);
                            let node = Node::Apply(head, address);
                            let read = self.intern_node(node.clone());
                            // A projection's selected-cell equation is producer
                            // metadata. Consult its exact key, without walking
                            // the memory history or choosing a term from facts.
                            if let Some(source) =
                                crate::kernel::prelude::canonical_load_projection_source(
                                    memory, pointer,
                                )
                            {
                                let source_head = self.intern_node(Node::AlgebraicMemoryRead(
                                    ty.clone(),
                                    source.read_identity(),
                                ));
                                let source_read =
                                    self.intern_node(Node::Apply(source_head, address));
                                self.close(vec![(read, source_read)]);
                            }
                            if let Some(origin) = crate::kernel::prelude::value_load_origin(
                                memory,
                                pointer,
                                crate::kernel::ABSTRACT_VALUE_WIDTH,
                            ) {
                                let origin_head = self.intern_node(Node::AlgebraicMemoryRead(
                                    ty,
                                    origin.read_identity(),
                                ));
                                let origin_read =
                                    self.intern_node(Node::Apply(origin_head, address));
                                self.close(vec![(read, origin_read)]);
                            }
                            node
                        }
                        // Match binds payload variables. Do not equate bodies
                        // by a signature that would forget their binding scope.
                        // A conditional is an atom by its whole identity, as a
                        // scalar conditional is.
                        N::Match { .. } | N::If { .. } => {
                            values.push(self.opaque_argument(&A::Algebraic(term.clone())));
                            continue;
                        }
                    }
                }
                Work::Field(field) => {
                    use crate::kernel::AlgebraicValue as V;
                    match field {
                        // A value of an abstract type is its algebraic term,
                        // so a field holding one is congruent with a field
                        // holding an equal one.
                        V::C(CValue::Parameter(term)) => pending.push(Work::Algebraic(term)),
                        V::C(value) => pending.push(Work::Value(value)),
                        V::Algebraic(term) => pending.push(Work::Algebraic(term)),
                        V::Integer(term) => {
                            pending.push(Work::Wrap(ArgumentTag::Integer));
                            pending.push(Work::Integer(term));
                        }
                    }
                    continue;
                }
                Work::Machine(term, width) => {
                    // σ(x) is `x`'s 32-bit word (rule K1): one class.
                    let term = if width == W::Bits32 {
                        term.word32()
                    } else {
                        term
                    };
                    let wide = width == W::Bits64;

                    let binary = if wide {
                        uint64_binary(term).map(|(op, a, b)| (Binary::UInt64(op), a, b))
                    } else if width == W::Bits32 {
                        // The e-graph reads a 32-bit sign-free operator as
                        // the word operator it computes, at either format
                        // (rule K1, until σ is a node of its own).
                        match term {
                            binary_term!(Bits32, Add, a, b) => {
                                Some((Binary::Int32Add, a.as_ref(), b.as_ref()))
                            }
                            binary_term!(UInt32, Divide, a, b) => Some((
                                Binary::Int32(Int32Binary::UnsignedDivide),
                                a.as_ref(),
                                b.as_ref(),
                            )),
                            binary_term!(UInt32, Remainder, a, b) => Some((
                                Binary::Int32(Int32Binary::UnsignedRemainder),
                                a.as_ref(),
                                b.as_ref(),
                            )),
                            binary_term!(Bits32, BitwiseXor, a, b) => Some((
                                Binary::Int32(Int32Binary::BitwiseXor),
                                a.as_ref(),
                                b.as_ref(),
                            )),
                            _ => term
                                .as_binary()
                                .filter(|(op, _, _)| op.is_bitvector32())
                                .map(|(op, a, b)| {
                                    (Binary::Int32(Int32Binary::Other(word_operator(op))), a, b)
                                }),
                        }
                    } else {
                        None
                    };
                    // A conversion into a narrow format: its node, and its
                    // word under rule K7 in the same class.
                    if width == W::Bits32
                        && let T::MachineIntegerCast {
                            value,
                            source,
                            destination,
                        } = term
                        && representation::narrow_carrier_mask(*destination).is_some()
                        && source.format().bits() <= 64
                    {
                        pending.push(Work::NarrowCast {
                            source: *source,
                            destination: *destination,
                            inverse: constants::signed_byte_load_operand(term).is_some(),
                        });
                        pending.push(Work::Machine(value, W::of_machine_type(*source)));
                        continue;
                    }
                    if width == W::Bits32 {
                        let unary = if let unary_term!(Bits32, BitwiseNot, value) = term {
                            Some((Int32Unary::Not, value.as_ref(), false))
                        } else {
                            constants::word_cast_operand(term).map(
                                |(value, source, destination)| {
                                    (
                                        Int32Unary::Cast(source, destination),
                                        value,
                                        constants::signed_byte_load_operand(term).is_some(),
                                    )
                                },
                            )
                        };
                        if let Some((op, value, inverse)) = unary {
                            pending.push(Work::Unary(op, inverse));
                            pending.push(Work::Machine(value, W::Bits32));
                            continue;
                        }
                    }
                    if let Some((op, a, b)) = binary {
                        if !wide {
                            crate::instrumentation::record_deterministic_work(1);
                        }
                        pending.push(Work::Binary(op));
                        pending.push(Work::Machine(b, width));
                        pending.push(Work::Machine(a, width));
                        continue;
                    }
                    if let Some((op, a, b)) = term.as_binary()
                        && !op.is_float()
                        && width
                            == if op.is_bitvector32() {
                                W::Bits32
                            } else {
                                W::Bits64
                            }
                    {
                        let head = self.intern_node(Node::MachineBinary(op, width));
                        pending.push(Work::Call(head, 2));
                        // Wide shifts admit independently promoted counts. Without
                        // a source width, retain the complete count identity rather
                        // than guessing its carrier from the shifted value.
                        if matches!(
                            op,
                            crate::kernel::BitvectorBinaryOp::Machine(
                                MachineIntegerType::Int64 | MachineIntegerType::UInt64,
                                MachineBinaryOp::ShiftLeft | MachineBinaryOp::ShiftRight
                            )
                        ) {
                            pending.push(Work::OpaqueCount(b));
                        } else {
                            pending.push(Work::Machine(b, width));
                        }
                        pending.push(Work::Machine(a, width));
                        continue;
                    }
                    if let Some((op, value)) = term.as_unary()
                        && !matches!(op, U::Float32Negate | U::Float64Negate)
                        && width
                            == match op {
                                U::Machine(
                                    crate::kernel::MachineIntegerType::Int32,
                                    crate::kernel::MachineUnaryOp::BitwiseNot,
                                )
                                | U::UInt32From64 => W::Bits32,
                                U::MachineIntegerCast { destination, .. } => {
                                    W::of_machine_type(destination)
                                }
                                _ => W::Bits64,
                            }
                    {
                        let source = match op {
                            U::Int64From32
                            | U::UInt64From32
                            | U::Int64FromUInt32
                            | U::UInt64FromInt32
                            | U::Machine(
                                crate::kernel::MachineIntegerType::Int32,
                                crate::kernel::MachineUnaryOp::BitwiseNot,
                            ) => W::Bits32,
                            U::UInt32From64 | U::UInt64FromInt64 => W::Bits64,
                            U::Machine(format, _) => W::of_machine_type(format),
                            U::MachineIntegerCast { source, .. } => W::of_machine_type(source),
                            U::Float32Negate | U::Float64Negate => unreachable!(),
                        };
                        let head = self.intern_node(Node::MachineUnary(op, width));
                        pending.push(Work::Call(head, 1));
                        pending.push(Work::Machine(value, source));
                        continue;
                    }
                    if let T::IntegerToMachine { value, destination } = term
                        && width == W::of_machine_type(*destination)
                    {
                        let head = self.intern_node(Node::IntegerToMachine(*destination));
                        pending.push(Work::Call(head, 1));
                        pending.push(Work::Integer(value));
                        continue;
                    }
                    // Rule C1: the cast `b as F`, a head applied to `b`'s
                    // class, linked with it and with the constants 0 and 1.
                    if let T::BoolCast { to, value } = term
                        && width == W::of_machine_type(*to)
                        && let Some(condition) = self.bool_node(value)
                    {
                        let head = self.intern_node(Node::BoolCast(*to));
                        let cast = self.intern_node(Node::Apply(head, condition));
                        let constant = |value: u32| match width {
                            W::Bits64 if to.format().is_signed() => {
                                T::Int64Constant(i64::from(value))
                            }
                            W::Bits64 => T::UInt64Constant(u64::from(value)),
                            _ => T::Constant(value),
                        };
                        if width != W::Bits128 {
                            let zero = self.intern_typed_machine(&constant(0), width);
                            let one = self.intern_typed_machine(&constant(1), width);
                            self.link_bool_cast(cast, condition, zero, one);
                        }
                        values.push(cast);
                        continue;
                    }
                    if let T::ClickFunctionApplication { name, arguments } = term {
                        let symbol = SharedPureApplication::intern(format!("click:{name}"), vec![]);
                        let head = self.intern_node(Node::Function(symbol, width, arguments.len()));
                        pending.push(Work::Call(head, arguments.len()));
                        pending.extend(arguments.iter().rev().map(Work::Argument));
                        continue;
                    }
                    // Legacy applications carry no argument sorts. Keep
                    // them opaque instead of guessing a machine width.
                    if width == W::Bits128 {
                        Node::Machine128(MachineAtom::new(
                            crate::kernel::MachineIntegerType::UInt128,
                            term.clone(),
                        ))
                    } else if wide {
                        if let Some((memory, pointer)) = uint64_read(term) {
                            let address = self
                                .address(pointer.block.clone(), pointer.offset.clone())
                                .0;
                            let numeric = self.read_address(address);
                            let read =
                                self.intern_node(Node::UInt64Read(memory.read_identity(), numeric));
                            let snapshot = memory.read_identity();
                            let origin = match term {
                                T::Variable(variable) => super::load_origin(variable, &memory),
                                _ => None,
                            };
                            self.pending_cell_reads.push(super::PendingCellRead {
                                read,
                                memory,
                                origin,
                                pointer,
                                kind: super::CellRead::UInt64,
                                only: None,
                            });
                            Node::UInt64Read(snapshot, numeric)
                        } else if let Some(pointer) = term.address_pointer() {
                            values.push(self.numeric_address(pointer));
                            continue;
                        } else {
                            Node::UInt64(MachineAtom::uint64(term.clone()))
                        }
                    } else {
                        let value = match term {
                            T::MemoryLoad(memory, pointer, kind)
                                if *kind != crate::kernel::LoadKind::Int8 =>
                            {
                                // Exact observation naming, without a version walk:
                                // another snapshot needs its checked read bridge.
                                T::Variable(crate::kernel::eval::load_variable_for_exact_cell(
                                    memory,
                                    pointer,
                                    *kind,
                                    crate::kernel::load_term_access_width(memory, pointer, *kind),
                                ))
                            }
                            _ => term.clone(),
                        };
                        Node::Int32(MachineAtom::int32(value))
                    }
                }
                Work::Argument(argument) => {
                    match argument {
                        A::Value(value) => pending.push(Work::Value(value)),
                        A::Algebraic(term) => {
                            pending.push(Work::Wrap(ArgumentTag::Algebraic));
                            pending.push(Work::Algebraic(term));
                        }
                        A::Integer(term) => {
                            pending.push(Work::Wrap(ArgumentTag::Integer));
                            pending.push(Work::Integer(term));
                        }
                        A::ArrayRef {
                            memory,
                            pointer,
                            element_type,
                        } => {
                            pending.push(Work::Wrap(ArgumentTag::Array(
                                crate::kernel::intern_c_memory(memory.clone()).read_identity(),
                                *element_type,
                            )));
                            pending.push(Work::Value(pointer));
                        }
                    }
                    continue;
                }
                Work::Value(value) => {
                    let value = value.numeric_value();
                    let scalar = match value {
                        CValue::Bool(t) => Some((CType::Bool, t, W::Bits32)),
                        CValue::Int8(t) => Some((CType::Int8, t, W::Bits32)),
                        CValue::UInt8(t) => Some((CType::UInt8, t, W::Bits32)),
                        CValue::Int16(t) => Some((CType::Int16, t, W::Bits32)),
                        CValue::UInt16(t) => Some((CType::UInt16, t, W::Bits32)),
                        CValue::Int32(t) => Some((CType::Int32, t, W::Bits32)),
                        CValue::UInt32(t) => Some((CType::UInt32, t, W::Bits32)),
                        CValue::Int64(t) => Some((CType::Int64, t, W::Bits64)),
                        CValue::UInt64(t) => Some((CType::UInt64, t, W::Bits64)),
                        CValue::Int128(t) => Some((CType::Int128, t, W::Bits128)),
                        CValue::UInt128(t) => Some((CType::UInt128, t, W::Bits128)),
                        _ => None,
                    };
                    if let Some((ty, term, width)) = scalar {
                        pending.push(Work::Wrap(ArgumentTag::Value(ty)));
                        pending.push(Work::Machine(term, width));
                        continue;
                    }
                    if let CValue::Pointer(pointer) = value {
                        let address = self.numeric_address(pointer.pointer());
                        // Address, allocation origin and selected extent are
                        // distinct congruence operands. Only a complete value
                        // equality merges the latter two domains.
                        let root = self.designation_node(pointer.designation());
                        let extent = self.extent_node(pointer);
                        let metadata = pointer
                            .clone()
                            .with_address(crate::kernel::Pointer::null())
                            .with_designation(std::sync::Arc::new(crate::kernel::Pointer::null()))
                            .with_root_extent();
                        let head = self.opaque_argument(&A::Value(CValue::Pointer(metadata)));
                        let node = self.intern_node(Node::Apply(head, root));
                        let node = self.intern_node(Node::Apply(node, extent));
                        let node = self.intern_node(Node::Apply(node, address));
                        self.retain_pointer_value(node, pointer.clone());
                        values.push(node);
                        continue;
                    } else {
                        values.push(self.opaque_argument(&A::Value(value.clone())));
                        continue;
                    }
                }
                Work::Wrap(tag) => {
                    let value = values.pop().expect("argument value");
                    let tag = self.intern_node(Node::ArgumentTag(tag));
                    Node::Apply(tag, value)
                }
                Work::Call(mut head, count) => {
                    let constructor = self.constructor_heads.contains_key(&head);
                    for argument in values.split_off(values.len() - count) {
                        head = self.intern_node(Node::Apply(head, argument));
                    }
                    if constructor {
                        self.retain_constructor_application(head);
                    }
                    values.push(head);
                    continue;
                }
                Work::Unary(op, inverse) => {
                    let value = values.pop().expect("unary operand");
                    let node = self.intern_node(Node::Int32Unary(op, value));
                    if inverse {
                        self.register_byte_inverse(node, value);
                    }
                    // Rule K8, a relation: the 32-bit widening of a narrow
                    // value is that value's word, its canonical carrier.
                    if let Int32Unary::Cast(source, destination) = op
                        && crate::kernel::is_narrow_widening32(source, destination)
                    {
                        self.close(vec![(node, value)]);
                    }
                    values.push(node);
                    continue;
                }
                Work::NarrowCast {
                    source,
                    destination,
                    inverse,
                } => {
                    let value = values.pop().expect("cast operand");
                    let node = self.narrow_cast_node(source, destination, value, inverse);
                    values.push(node);
                    continue;
                }
                Work::Binary(op) => {
                    let b = values.pop().expect("right operand");
                    let a = values.pop().expect("left operand");
                    match op {
                        Binary::Int32Add => Node::Int32Add(a, b),
                        Binary::Int32(op) => Node::Int32Binary(op, a, b),
                        Binary::UInt64(op) => Node::UInt64Binary(op, a, b),
                    }
                }
            };
            let id = self.intern_node(node);
            if let Some(term) = scalar_source {
                self.register_scalar_witness(term, id);
            }
            values.push(id);
        }
        values.pop().expect("machine term")
    }

    /// The class of `Cast(source -> destination, v)` into an 8- or 16-bit
    /// format, given the class `value` of its operand `v`: the cast node,
    /// as every other conversion is interned (`Int32Unary::Cast` over a
    /// source of at most 32 bits, the applied `MachineUnary` over a 64-bit
    /// one), joined with the class of its word under rule K7
    /// (`representation::narrow_cast_word`): `w & m`, or `((w & m) ^ s) - s`
    /// for a signed destination, with `w` the operand's word or low word.
    ///
    /// The word is built from the operand's class, not from its term, so
    /// this adds at most five nodes and one merge whatever the operand's
    /// size, and a nested narrow cast is interned once. Its nodes are the
    /// ones the constructors' spelling of the word interns
    /// (`Bitvector32Term::bitwise_and`, `bitwise_xor`, `subtract`), so the
    /// written `x & 255u32` meets the cast's class.
    fn narrow_cast_node(
        &mut self,
        source: MachineIntegerType,
        destination: MachineIntegerType,
        value: u64,
        inverse: bool,
    ) -> u64 {
        let (node, carrier) = self.narrow_cast_with_word(source, destination, value, inverse);
        self.close(vec![(node, carrier)]);
        node
    }

    /// [`Self::narrow_cast_node`] with its rule-K7 union queued on `pending`
    /// instead of closed, for a caller that is closing already.
    pub(super) fn narrow_cast_parts(
        &mut self,
        source: MachineIntegerType,
        destination: MachineIntegerType,
        value: u64,
        pending: &mut PendingUnions,
    ) -> u64 {
        let (node, carrier) = self.narrow_cast_with_word(source, destination, value, false);
        pending.push((node, carrier));
        node
    }

    /// The narrow cast node and the class of its rule-K7 word, not yet
    /// joined.
    fn narrow_cast_with_word(
        &mut self,
        source: MachineIntegerType,
        destination: MachineIntegerType,
        value: u64,
        inverse: bool,
    ) -> (u64, u64) {
        use crate::kernel::BitvectorBinaryOp as B;
        crate::instrumentation::record_deterministic_work(1);
        let (mask, sign) = representation::narrow_carrier_mask(destination)
            .expect("a narrow destination has a carrier mask");
        let (node, word) = if source.format().bits() <= 32 {
            let node = self.intern_node(Node::Int32Unary(
                Int32Unary::Cast(source, destination),
                value,
            ));
            if inverse {
                self.register_byte_inverse(node, value);
            }
            (node, value)
        } else {
            let head = self.intern_node(Node::MachineUnary(
                U::MachineIntegerCast {
                    source,
                    destination,
                },
                W::Bits32,
            ));
            let node = self.intern_node(Node::Apply(head, value));
            let low = self.intern_node(Node::MachineUnary(U::UInt32From64, W::Bits32));
            (node, self.intern_node(Node::Apply(low, value)))
        };
        let mask = self.intern_typed_machine(&T::Constant(mask), W::Bits32);
        let mut carrier = self.intern_node(Node::Int32Binary(
            Int32Binary::Other(B::Machine(
                crate::kernel::MachineIntegerType::Int32,
                crate::kernel::MachineBinaryOp::BitwiseAnd,
            )),
            word,
            mask,
        ));
        if let Some(sign) = sign {
            // `bitwise_xor` orders a constant before the masked word.
            let sign = self.intern_typed_machine(&T::Constant(sign), W::Bits32);
            let flipped =
                self.intern_node(Node::Int32Binary(Int32Binary::BitwiseXor, sign, carrier));
            carrier = self.intern_node(Node::Int32Binary(
                Int32Binary::Other(B::Machine(
                    crate::kernel::MachineIntegerType::Int32,
                    crate::kernel::MachineBinaryOp::Subtract,
                )),
                flipped,
                sign,
            ));
        }
        (node, carrier)
    }

    fn algebraic_type_token(&mut self, ty: &crate::kernel::AlgebraicType) -> SharedPureApplication {
        use crate::kernel::AlgebraicValueType as V;
        enum Work<'a> {
            Type(&'a V),
            Call(u64, usize),
        }
        let head = self.intern_node(Node::TypeName(
            ty.rigid,
            ty.name.clone(),
            ty.arguments.len(),
        ));
        let mut pending = vec![Work::Call(head, ty.arguments.len())];
        pending.extend(ty.arguments.iter().rev().map(Work::Type));
        let mut values = Vec::new();
        while let Some(work) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            let node = match work {
                Work::Type(V::C(ty)) => Node::TypeC(*ty),
                Work::Type(V::ObjectPointer(ty, class)) => {
                    Node::TypeObjectPointer(*ty, class.clone())
                }
                Work::Type(V::Integer) => Node::TypeInteger,
                Work::Type(V::Parameter(name)) => Node::TypeName(true, name.clone(), 0),
                Work::Type(V::Algebraic { name, arguments }) => {
                    let head =
                        self.intern_node(Node::TypeName(false, name.clone(), arguments.len()));
                    pending.push(Work::Call(head, arguments.len()));
                    pending.extend(arguments.iter().rev().map(Work::Type));
                    continue;
                }
                Work::Call(mut head, count) => {
                    for argument in values.split_off(values.len() - count) {
                        head = self.intern_node(Node::Apply(head, argument));
                    }
                    values.push(head);
                    continue;
                }
            };
            values.push(self.intern_node(node));
        }
        let nominal = values.pop().expect("nominal type");
        let key = (ty.variants.as_ptr() as usize, nominal);
        if let Some((_, token)) = self.algebraic_types.get(&key) {
            return token.clone();
        }
        // Intern the full resolved root schema once per schema allocation and
        // nominal instantiation. Independently resolved equal types share a
        // token; identically named but different schemas do not.
        let token = SharedPureApplication::intern(
            "equality:algebraic-type".into(),
            vec![A::Algebraic(crate::kernel::AlgebraicTerm {
                algebraic_type: ty.clone(),
                node: crate::kernel::AlgebraicTermNode::Variable(Variable(0)),
            })],
        );
        self.algebraic_types
            .insert(key, (ty.variants.clone(), token.clone()));
        token
    }

    pub(super) fn algebraic_nodes(
        &mut self,
        a: &crate::kernel::AlgebraicTerm,
        b: &crate::kernel::AlgebraicTerm,
    ) -> Option<(u64, u64)> {
        if self.algebraic_type_token(&a.algebraic_type)
            != self.algebraic_type_token(&b.algebraic_type)
        {
            return None;
        }
        let a = self.intern_algebraic(a);
        let b = self.intern_algebraic(b);
        self.register_pending_loads();
        Some((a, b))
    }

    pub(in crate::kernel::equality_graph) fn are_algebraic_equal(
        &mut self,
        a: &crate::kernel::AlgebraicTerm,
        b: &crate::kernel::AlgebraicTerm,
    ) -> bool {
        self.algebraic_nodes(a, b)
            .is_some_and(|(a, b)| self.root(a) == self.root(b))
    }

    pub(in crate::kernel::equality_graph) fn add_algebraic_equality(
        &mut self,
        a: &crate::kernel::AlgebraicTerm,
        b: &crate::kernel::AlgebraicTerm,
    ) -> bool {
        let Some((left, right)) = self.algebraic_nodes(a, b) else {
            return false;
        };
        let changed = self.close(vec![(left, right)]);
        for (node, term) in [(left, a), (right, b)] {
            if matches!(
                term.node,
                crate::kernel::AlgebraicTermNode::Constructor { .. }
            ) {
                let root = self.root(node);
                if !self.algebraic_constructors.contains_key(&root) {
                    self.algebraic_constructors
                        .insert(root, Arc::new(term.clone()));
                }
            }
        }
        changed
    }

    pub(in crate::kernel::equality_graph) fn known_algebraic_constructor(
        &mut self,
        model: &crate::kernel::AlgebraicTerm,
    ) -> Option<crate::kernel::AlgebraicTerm> {
        let node = self.intern_algebraic(model);
        self.register_pending_loads();
        self.algebraic_constructors
            .get(&self.root(node))
            .map(|constructor| constructor.as_ref().clone())
    }

    pub(in crate::kernel::equality_graph) fn add_pointer_value_equality(
        &mut self,
        a: &crate::kernel::CPointerValue,
        b: &crate::kernel::CPointerValue,
    ) -> bool {
        let roots = (
            self.designation_node(a.designation()),
            self.designation_node(b.designation()),
        );
        let extents = (self.extent_node(a), self.extent_node(b));
        let a = self.intern_expression(None, None, None, Some(&CValue::Pointer(a.clone())), None);
        let b = self.intern_expression(None, None, None, Some(&CValue::Pointer(b.clone())), None);
        self.register_pending_loads();
        self.close(vec![roots, extents, (a, b)])
    }

    pub(in crate::kernel::equality_graph) fn merge_pointer_read_domains(
        &mut self,
        a: &crate::kernel::Pointer,
        b: &crate::kernel::Pointer,
    ) -> bool {
        if self.read_domains.equal(a, b) {
            return false;
        }
        let left = self.read_domains.representative(a);
        let right = self.read_domains.representative(b);
        self.read_domains.insert(a, b, |a, _| a.clone());
        let joined = self.read_domains.representative(a);
        // A source registration need not manufacture congruence applications.
        // Merge just the domain nodes that selected consumers already named;
        // later consumers select the retained domain representative directly.
        let mut pending = Vec::new();
        for nodes in [
            &mut self.read_designation_nodes,
            &mut self.read_extent_nodes,
        ] {
            let a = nodes.get(&left).copied();
            let b = nodes.get(&right).copied();
            nodes.remove(&left);
            nodes.remove(&right);
            if let Some(node) = a.or(b) {
                nodes.insert(joined.clone(), node);
            }
            if let (Some(a), Some(b)) = (a, b) {
                pending.push((a, b));
            }
        }
        self.close(pending);
        true
    }

    pub(in crate::kernel::equality_graph) fn merge_designations(
        &mut self,
        a: &crate::kernel::Pointer,
        b: &crate::kernel::Pointer,
    ) -> bool {
        let a = self.designation_node(a);
        let b = self.designation_node(b);
        self.close(vec![(a, b)])
    }

    pub(in crate::kernel::equality_graph) fn designations_equal(
        &mut self,
        a: &crate::kernel::Pointer,
        b: &crate::kernel::Pointer,
    ) -> bool {
        let a = self.designation_node(a);
        let b = self.designation_node(b);
        self.register_pending_loads();
        self.root(a) == self.root(b)
    }

    pub(in crate::kernel::equality_graph) fn pointer_values_equal(
        &mut self,
        a: &crate::kernel::CPointerValue,
        b: &crate::kernel::CPointerValue,
    ) -> bool {
        let a = self.intern_expression(None, None, None, Some(&CValue::Pointer(a.clone())), None);
        let b = self.intern_expression(None, None, None, Some(&CValue::Pointer(b.clone())), None);
        self.register_pending_loads();
        self.root(a) == self.root(b)
    }

    pub(super) fn retain_pointer_value(&mut self, node: u64, value: crate::kernel::CPointerValue) {
        let root = self.root(node);
        let value = self
            .pointer_values
            .get(&root)
            .map_or(value.clone(), |previous| {
                crate::kernel::pointer_designations::prefer_pointer(previous, &value)
            });
        self.pointer_values.insert(root, value);
    }

    pub(in crate::kernel::equality_graph) fn pointer_value_representative(
        &mut self,
        value: &crate::kernel::CPointerValue,
    ) -> crate::kernel::CPointerValue {
        let node = self.intern_expression(
            None,
            None,
            None,
            Some(&CValue::Pointer(value.clone())),
            None,
        );
        self.register_pending_loads();
        let representative = self
            .pointer_values
            .get(&self.root(node))
            .unwrap_or(value)
            .clone();
        if representative.extent_is_known() {
            return representative;
        }
        let extent = self.extent_node(value);
        let Some(witness) = self.extent_values.get(&self.root(extent)) else {
            return representative;
        };
        if !witness.extent_is_known() {
            return representative;
        }
        let adopted = representative
            .with_extent(witness.extent().cloned())
            .with_opaque_extent(witness.opaque_extent().cloned().map(std::sync::Arc::new));
        if witness.extent().is_none() {
            adopted.with_root_extent()
        } else {
            adopted
        }
    }

    fn extent_node(&mut self, value: &crate::kernel::CPointerValue) -> u64 {
        let node = if let Some(extent) = value.extent() {
            let head = self.intern_node(Node::ArgumentTag(ArgumentTag::PointerSubobjectExtent));
            let width = self.intern_int32(&extent.width);
            let head = self.intern_node(Node::Apply(head, width));
            let start = self
                .address(extent.start.block.clone(), extent.start.offset.clone())
                .0;
            self.intern_node(Node::Apply(head, start))
        } else if value.extent_is_known() {
            self.intern_node(Node::ArgumentTag(ArgumentTag::PointerRootExtent))
        } else {
            self.opaque_extent_node(value.opaque_extent().unwrap_or(value.designation()))
        };
        let root = self.root(node);
        let witness = self
            .extent_values
            .get(&root)
            .map_or(value.clone(), |previous| {
                crate::kernel::pointer_designations::prefer_pointer(previous, value)
            });
        self.extent_values.insert(root, witness);
        node
    }

    fn opaque_extent_node(&mut self, origin: &crate::kernel::Pointer) -> u64 {
        let node = self.opaque_extent_node_without_calls(origin);
        self.retain_pointer_call_component(origin, node, ArgumentTag::PointerCallExtent);
        node
    }

    fn opaque_extent_node_without_calls(&mut self, origin: &crate::kernel::Pointer) -> u64 {
        let origin = self.read_domains.representative(origin);
        if let Some(node) = self.read_extent_nodes.get(&origin) {
            return *node;
        }
        if let Some(read) = origin.as_loaded_value() {
            let source = crate::kernel::prelude::canonical_load_projection_source(
                &read.defining_memory,
                &read.defining_address,
            )
            .unwrap_or(read.defining_memory);
            let cell = self
                .address(read.defining_address.block, read.defining_address.offset)
                .0;
            let head = self.intern_node(Node::ArgumentTag(ArgumentTag::PointerExtentRead(
                source.read_identity(),
            )));
            let node = self.intern_node(Node::Apply(head, cell));
            self.read_extent_nodes.insert(origin, node);
            return node;
        }
        self.intern_node(Node::OpaqueArgument(SharedPureApplication::intern(
            "<pointer-extent-origin>".into(),
            vec![A::Value(CValue::Pointer(
                crate::kernel::CPointerValue::new(origin.clone(), CType::VoidPointer),
            ))],
        )))
    }

    /// Only a complete pointer-value equality can connect an opaque extent
    /// to the root-extent tag. Numeric address equality cannot do so.
    pub(in crate::kernel::equality_graph) fn opaque_extent_is_root(
        &mut self,
        origin: &crate::kernel::Pointer,
    ) -> bool {
        let extent = self.opaque_extent_node(origin);
        let root = self.intern_node(Node::ArgumentTag(ArgumentTag::PointerRootExtent));
        self.register_pending_loads();
        self.root(extent) == self.root(root)
    }

    pub(in crate::kernel::equality_graph) fn opaque_extents_equal(
        &mut self,
        a: &crate::kernel::Pointer,
        b: &crate::kernel::Pointer,
    ) -> bool {
        let a = self.opaque_extent_node(a);
        let b = self.opaque_extent_node(b);
        self.register_pending_loads();
        self.root(a) == self.root(b)
    }

    fn designation_node(&mut self, origin: &crate::kernel::Pointer) -> u64 {
        let node = self.designation_node_without_calls(origin);
        self.retain_pointer_call_component(origin, node, ArgumentTag::PointerCallDesignation);
        node
    }

    /// Complete result domains depend on complete arguments. Their parallel
    /// function head never joins raw output-address equations. Queue the one
    /// selected identity definition so nested calls stay iterative.
    fn retain_pointer_call_component(
        &mut self,
        origin: &crate::kernel::Pointer,
        component: u64,
        tag: ArgumentTag,
    ) {
        let PointerBlock::PureFunctionApplication(application) = &origin.block else {
            return;
        };
        // This internal constructor names numeric coordinates only. Equal
        // words cannot identify the designation or bounds of their casts.
        if application.integer_address_bits().is_some() {
            return;
        }
        if origin.offset != PointerOffsetTerm::Constant(0) {
            return;
        }
        let key = Node::PointerFunctionIdentity(application.clone());
        let new = !self.nodes.contains_key(&key);
        let identity = self.intern_node(key);
        if new {
            self.pending_pointer_identities
                .push((identity, application.clone()));
        }
        let head = self.intern_node(Node::ArgumentTag(tag));
        let projected = self.intern_node(Node::Apply(head, identity));
        self.close_with_affine_definition(vec![(component, projected)], true);
    }

    fn designation_node_without_calls(&mut self, origin: &crate::kernel::Pointer) -> u64 {
        // Congruence here uses the cell a complete pointer was read from.
        // Equality of the loaded pointer's numeric address never merges this
        // node with a different value origin.
        let origin = self.read_domains.representative(origin);
        if let Some(node) = self.read_designation_nodes.get(&origin) {
            return *node;
        }
        if let crate::kernel::PointerBlock::LoadedPointer(identity) = &origin.block
            && let Some((memory, cell)) = crate::kernel::eval::registered_pointer_load(*identity)
        {
            let source = crate::kernel::prelude::canonical_load_projection_source(&memory, &cell)
                .unwrap_or(memory);
            let cell = self.address(cell.block, cell.offset).0;
            let head = self.intern_node(Node::ArgumentTag(ArgumentTag::DesignationRead(
                source.read_identity(),
            )));
            let node = self.intern_node(Node::Apply(head, cell));
            self.read_designation_nodes.insert(origin, node);
            return node;
        }
        self.opaque_argument(&A::Value(CValue::Pointer(
            crate::kernel::CPointerValue::new(origin.clone(), CType::VoidPointer),
        )))
    }

    fn opaque_argument(&mut self, argument: &A) -> u64 {
        // Map comparisons use stable IDs, not full algebraic values/snapshots.
        self.intern_node(Node::OpaqueArgument(SharedPureApplication::intern(
            String::new(),
            vec![argument.clone()],
        )))
    }

    pub(in crate::kernel::equality_graph) fn condition_node(
        &mut self,
        condition: &C,
    ) -> Option<u64> {
        use ConditionKind::*;
        let (kind, left, right) = match condition {
            C::IntegerEqual(a, b) => (IntegerEq, self.intern_integer(a), self.intern_integer(b)),
            C::IntegerNotEqual(a, b) => (IntegerNe, self.intern_integer(a), self.intern_integer(b)),
            C::IntegerLessThan(a, b) => (IntegerLt, self.intern_integer(a), self.intern_integer(b)),
            C::IntegerLessEqual(a, b) => {
                (IntegerLe, self.intern_integer(a), self.intern_integer(b))
            }
            C::IntegerGreaterThan(a, b) => {
                (IntegerGt, self.intern_integer(a), self.intern_integer(b))
            }
            C::IntegerGreaterEqual(a, b) => {
                (IntegerGe, self.intern_integer(a), self.intern_integer(b))
            }
            C::AlgebraicEqual(a, b) => {
                let (a, b) = self.algebraic_nodes(a, b)?;
                (AlgebraicEq, a, b)
            }
            C::Compare {
                format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                relation: CompareRelation::Equal,
                left: a,
                right: b,
            } => (Int32Eq, self.intern_int32(a), self.intern_int32(b)),
            C::Overflows {
                format: MachineIntegerType::Int32,
                op: OverflowOperation::Add,
                left: a,
                right: b,
            } => (Int32AddOverflow, self.intern_int32(a), self.intern_int32(b)),
            C::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left: a,
                right: b,
            } => (Int32Lt, self.intern_int32(a), self.intern_int32(b)),
            C::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left: a,
                right: b,
            } => (Int32Le, self.intern_int32(a), self.intern_int32(b)),
            C::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterThan,
                left: a,
                right: b,
            } => (Int32Gt, self.intern_int32(a), self.intern_int32(b)),
            C::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterEqual,
                left: a,
                right: b,
            } => (Int32Ge, self.intern_int32(a), self.intern_int32(b)),
            C::Compare {
                format: MachineIntegerType::UInt32,
                relation:
                    relation @ (crate::kernel::CompareRelation::LessThan
                    | crate::kernel::CompareRelation::LessEqual
                    | crate::kernel::CompareRelation::GreaterThan
                    | crate::kernel::CompareRelation::GreaterEqual),
                left: a,
                right: b,
            } if *relation != CompareRelation::Equal => (
                Self::condition_kind(condition)?,
                self.intern_int32(a),
                self.intern_int32(b),
            ),
            C::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left: a,
                right: b,
            } => (UInt64Eq, self.intern_uint64(a), self.intern_uint64(b)),
            C::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::LessThan,
                left: a,
                right: b,
            } => (Int64Lt, self.intern_uint64(a), self.intern_uint64(b)),
            C::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::LessEqual,
                left: a,
                right: b,
            } => (Int64Le, self.intern_uint64(a), self.intern_uint64(b)),
            C::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::GreaterThan,
                left: a,
                right: b,
            } => (Int64Gt, self.intern_uint64(a), self.intern_uint64(b)),
            C::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::GreaterEqual,
                left: a,
                right: b,
            } => (Int64Ge, self.intern_uint64(a), self.intern_uint64(b)),
            C::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::LessThan,
                left: a,
                right: b,
            } => (UInt64Lt, self.intern_uint64(a), self.intern_uint64(b)),
            C::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::LessEqual,
                left: a,
                right: b,
            } => (UInt64Le, self.intern_uint64(a), self.intern_uint64(b)),
            C::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::GreaterThan,
                left: a,
                right: b,
            } => (UInt64Gt, self.intern_uint64(a), self.intern_uint64(b)),
            C::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::GreaterEqual,
                left: a,
                right: b,
            } => (UInt64Ge, self.intern_uint64(a), self.intern_uint64(b)),
            C::PointerValueEqual(a, b) => (
                PointerValueEq,
                self.intern_expression(
                    None,
                    None,
                    None,
                    Some(&CValue::Pointer((**a).clone())),
                    None,
                ),
                self.intern_expression(
                    None,
                    None,
                    None,
                    Some(&CValue::Pointer((**b).clone())),
                    None,
                ),
            ),
            C::PointerEqual(a, b) => (
                PointerEq,
                self.address(a.block.clone(), a.offset.clone()).0,
                self.address(b.block.clone(), b.offset.clone()).0,
            ),
            C::PointerOffsetEqual(a, b) => (OffsetEq, self.intern(a), self.intern(b)),
            C::BoolApplication(_) | C::BoolIf { .. } | C::BoolEqual(..) | C::BoolLoad(..) => {
                return self.bool_node(condition);
            }
            _ => return None,
        };
        let node = self.intern_node(Node::Condition(kind, left, right));
        if let C::PointerEqual(a, b) = condition
            && a.block == b.block
        {
            // These are two views of the same predicate, not a new premise.
            // Retaining both avoids reconstructing a cancelled base from an
            // arbitrary representative after later pointer aliases merge.
            let a = self.intern(&a.offset);
            let b = self.intern(&b.offset);
            let offsets = self.intern_node(Node::Condition(OffsetEq, a, b));
            self.close(vec![(node, offsets)]);
        }
        Some(node)
    }

    fn condition_kind(condition: &C) -> Option<ConditionKind> {
        Some(match condition {
            C::IntegerEqual(..) => ConditionKind::IntegerEq,
            C::IntegerNotEqual(..) => ConditionKind::IntegerNe,
            C::IntegerLessThan(..) => ConditionKind::IntegerLt,
            C::IntegerLessEqual(..) => ConditionKind::IntegerLe,
            C::IntegerGreaterThan(..) => ConditionKind::IntegerGt,
            C::IntegerGreaterEqual(..) => ConditionKind::IntegerGe,
            C::AlgebraicEqual(..) => ConditionKind::AlgebraicEq,
            C::Compare {
                format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                relation: CompareRelation::Equal,
                ..
            } => ConditionKind::Int32Eq,
            C::Overflows {
                format: MachineIntegerType::Int32,
                op: OverflowOperation::Add,
                ..
            } => ConditionKind::Int32AddOverflow,
            C::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                ..
            } => ConditionKind::UInt64Eq,
            C::PointerEqual(..) => ConditionKind::PointerEq,
            C::PointerValueEqual(..) => ConditionKind::PointerValueEq,
            C::PointerOffsetEqual(..) => ConditionKind::OffsetEq,
            C::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                ..
            } => ConditionKind::Int32Lt,
            C::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                ..
            } => ConditionKind::Int32Le,
            C::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterThan,
                ..
            } => ConditionKind::Int32Gt,
            C::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterEqual,
                ..
            } => ConditionKind::Int32Ge,
            C::Compare {
                format: MachineIntegerType::UInt32,
                relation: CompareRelation::LessThan,
                ..
            } => ConditionKind::UInt32Lt,
            C::Compare {
                format: MachineIntegerType::UInt32,
                relation: CompareRelation::LessEqual,
                ..
            } => ConditionKind::UInt32Le,
            C::Compare {
                format: MachineIntegerType::UInt32,
                relation: CompareRelation::GreaterThan,
                ..
            } => ConditionKind::UInt32Gt,
            C::Compare {
                format: MachineIntegerType::UInt32,
                relation: CompareRelation::GreaterEqual,
                ..
            } => ConditionKind::UInt32Ge,
            C::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::LessThan,
                ..
            } => ConditionKind::Int64Lt,
            C::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::LessEqual,
                ..
            } => ConditionKind::Int64Le,
            C::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::GreaterThan,
                ..
            } => ConditionKind::Int64Gt,
            C::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::GreaterEqual,
                ..
            } => ConditionKind::Int64Ge,
            C::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::LessThan,
                ..
            } => ConditionKind::UInt64Lt,
            C::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::LessEqual,
                ..
            } => ConditionKind::UInt64Le,
            C::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::GreaterThan,
                ..
            } => ConditionKind::UInt64Gt,
            C::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::GreaterEqual,
                ..
            } => ConditionKind::UInt64Ge,
            C::BoolEqual(..) => ConditionKind::BoolEq,
            C::BoolApplication(_) | C::BoolIf { .. } | C::BoolLoad(..) => ConditionKind::BoolValue,
            _ => return None,
        })
    }

    /// The class of a `Bool` value (`design/machine-integers.md`, Stage 5).
    ///
    /// A literal is one class per value, annotated with its truth; a binder
    /// is its variable's class; an application is a call of its function's
    /// head on its argument classes, so applications to equal arguments are
    /// congruent; a conditional is a call of one head on its three classes;
    /// an equality is the condition node `BoolEq` on its operands' classes,
    /// true when they meet (rule L-Eq); a read is its snapshot's read head
    /// applied to its address class. A comparison is its own condition node.
    /// Each node is interned once, so the work is the value's size. `None`
    /// for a condition the graph does not intern.
    pub(in crate::kernel::equality_graph) fn bool_node(&mut self, condition: &C) -> Option<u64> {
        let node = match condition {
            C::Constant(value) => {
                let node = self.intern_node(Node::BoolConstant(*value));
                self.retain_condition_truth(node, if *value { 1 } else { 2 });
                node
            }
            C::Variable(variable) => {
                let fresh = !self.nodes.contains_key(&Node::BoolVariable(*variable));
                let node = self.intern_node(Node::BoolVariable(*variable));
                if fresh && let Some(truth) = self.bool_binder_truth.get(variable).copied() {
                    self.retain_condition_truth(node, truth);
                }
                node
            }
            C::BoolApplication(application) => self.intern_bool_call(application),
            C::BoolIf {
                condition,
                then_condition,
                else_condition,
            } => {
                let mut node = self.intern_node(Node::BoolIf);
                for operand in [condition, then_condition, else_condition] {
                    let operand = self.bool_node(operand)?;
                    node = self.intern_node(Node::Apply(node, operand));
                }
                node
            }
            C::BoolEqual(left, right) => {
                let left = self.bool_node(left)?;
                let right = self.bool_node(right)?;
                self.intern_node(Node::Condition(ConditionKind::BoolEq, left, right))
            }
            C::BoolLoad(memory, pointer) => {
                let head = self.intern_node(Node::BoolRead(memory.read_identity()));
                let address = self
                    .address(pointer.block.clone(), pointer.offset.clone())
                    .0;
                self.intern_node(Node::Apply(head, address))
            }
            condition => self.condition_node(condition)?,
        };
        Some(node)
    }

    /// Admit a fact about a `Bool` value: its class's truth, and for a true
    /// equality the merge of its operands' classes (rule L-Eq). A binder's
    /// fact is admitted only once some `Bool` value has interned the binder,
    /// so a fact no `Bool` value names adds nothing. One node per subterm,
    /// one merge.
    pub(in crate::kernel::equality_graph) fn admit_bool_condition(
        &mut self,
        condition: &C,
        value: bool,
    ) -> bool {
        let truth = if value { 1 } else { 2 };
        let node = match condition {
            C::Variable(variable) => {
                let known = self.bool_binder_truth.get(variable).copied().unwrap_or(0);
                if known | truth != known {
                    self.bool_binder_truth.insert(*variable, known | truth);
                }
                match self.nodes.get(&Node::BoolVariable(*variable)) {
                    Some(node) => *node,
                    None => return false,
                }
            }
            C::BoolApplication(_) | C::BoolIf { .. } | C::BoolEqual(..) | C::BoolLoad(..) => {
                let Some(node) = self.bool_node(condition) else {
                    return false;
                };
                self.condition_kinds = self.condition_kinds.with_value((
                    Self::condition_kind(condition).expect("a `Bool` value has a kind"),
                    value,
                ));
                node
            }
            _ => return false,
        };
        self.register_pending_loads();
        if let (C::BoolEqual(..), true) = (condition, value)
            && let Some(Application::Condition(_, left, right)) =
                self.applications.get(&node).copied()
        {
            self.close(vec![(left, right)]);
        }
        self.retain_condition_truth(node, truth);
        true
    }

    /// Whether a `Bool` binder's class has the truth `value`, which an L-Eq
    /// merge can give it. A binder no `Bool` value has interned is not
    /// looked at further: its own facts are the fact context's.
    pub(in crate::kernel::equality_graph) fn knows_bool_binder(
        &self,
        variable: crate::kernel::Variable,
        value: bool,
    ) -> bool {
        let Some(node) = self.nodes.get(&Node::BoolVariable(variable)).copied() else {
            return false;
        };
        let truth = if value { 1 } else { 2 };
        self.condition_truth
            .get(&self.root(node))
            .is_some_and(|known| known & truth != 0)
    }

    /// Whether the graph holds `ConditionIs(condition, value)` for a `Bool`
    /// value: its class's truth, or for a true equality its operands' meeting.
    pub(in crate::kernel::equality_graph) fn knows_bool_condition(
        &mut self,
        condition: &C,
        value: bool,
    ) -> bool {
        let Some(node) = self.bool_node(condition) else {
            return false;
        };
        self.register_pending_loads();
        let truth = if value { 1 } else { 2 };
        if self
            .condition_truth
            .get(&self.root(node))
            .is_some_and(|known| known & truth != 0)
        {
            return true;
        }
        if let (C::BoolEqual(..), true) = (condition, value)
            && let Some(Application::Condition(_, left, right)) =
                self.applications.get(&node).copied()
        {
            return self.root(left) == self.root(right);
        }
        false
    }

    pub(in crate::kernel::equality_graph) fn may_know_condition(
        &self,
        condition: &C,
        value: bool,
    ) -> bool {
        Self::condition_kind(condition).is_some_and(|kind| {
            self.condition_kinds.contains(&(kind, value))
                || (kind == ConditionKind::OffsetEq
                    && self
                        .condition_kinds
                        .contains(&(ConditionKind::PointerEq, value)))
                || (kind == ConditionKind::PointerEq
                    && self
                        .condition_kinds
                        .contains(&(ConditionKind::OffsetEq, value)))
        })
    }

    pub(in crate::kernel::equality_graph) fn admit_condition(
        &mut self,
        condition: &C,
        value: bool,
    ) -> bool {
        let Some(node) = self.condition_node(condition) else {
            return false;
        };
        self.condition_kinds = self.condition_kinds.with_value((
            Self::condition_kind(condition).expect("supported condition"),
            value,
        ));
        self.register_pending_loads();
        // Only signed 32-bit order facts contribute to this interval. Wide
        // and unsigned comparisons retain their separate semantic orders.
        let order = match (condition, value) {
            (
                C::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessThan,
                    left: a,
                    right: b,
                },
                true,
            )
            | (
                C::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessEqual,
                    left: a,
                    right: b,
                },
                false,
            ) => Some((a, b, true, value)),
            (
                C::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessEqual,
                    left: a,
                    right: b,
                },
                true,
            )
            | (
                C::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessThan,
                    left: a,
                    right: b,
                },
                false,
            ) => Some((a, b, false, value)),
            (
                C::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::GreaterThan,
                    left: a,
                    right: b,
                },
                true,
            )
            | (
                C::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::GreaterEqual,
                    left: a,
                    right: b,
                },
                false,
            ) => Some((b, a, true, value)),
            (
                C::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::GreaterEqual,
                    left: a,
                    right: b,
                },
                true,
            )
            | (
                C::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::GreaterThan,
                    left: a,
                    right: b,
                },
                false,
            ) => Some((b, a, false, value)),
            _ => None,
        };
        if let Some((a, b, strict, forward)) = order {
            let (a, b) = if forward { (a, b) } else { (b, a) };
            if let Some(bound) = b.as_const() {
                self.retain_signed_int32_interval(
                    a,
                    i64::from(i32::MIN),
                    i64::from(bound as i32) - i64::from(strict),
                );
            }
            if let Some(bound) = a.as_const() {
                self.retain_signed_int32_interval(
                    b,
                    i64::from(bound as i32) + i64::from(strict),
                    i64::from(i32::MAX),
                );
            }
        }
        self.retain_condition_truth(node, if value { 1 } else { 2 });
        true
    }

    pub(in crate::kernel::equality_graph) fn knows_condition(
        &mut self,
        condition: &C,
        value: bool,
    ) -> bool {
        let Some(node) = self.condition_node(condition) else {
            return false;
        };
        self.register_pending_loads();
        let truth = if value { 1 } else { 2 };
        if self
            .condition_truth
            .get(&self.root(node))
            .is_some_and(|known| known & truth != 0)
        {
            return true;
        }
        let C::PointerOffsetEqual(a, b) = condition else {
            return false;
        };
        let left = self.intern(a);
        let right = self.intern(b);
        let (Some(left), Some(right)) = (
            self.addresses_by_offset.get(&self.root(left)).cloned(),
            self.addresses_by_offset.get(&self.root(right)).cloned(),
        ) else {
            return false;
        };
        // A common block makes this the same address predicate. Nominate only
        // addresses registered at these offsets, never scan ambient pointer facts
        // or infer offset disequality merely from distinct allocation identities.
        let (small, large) = if left.len() <= right.len() {
            (left, right)
        } else {
            (right, left)
        };
        for (block, a) in small.iter() {
            crate::instrumentation::record_deterministic_work(1);
            if let Some(b) = large.get(block) {
                for (a, b) in [(*a, *b), (*b, *a)] {
                    let address_condition =
                        self.intern_node(Node::Condition(ConditionKind::PointerEq, a, b));
                    if self
                        .condition_truth
                        .get(&self.root(address_condition))
                        .is_some_and(|known| known & truth != 0)
                    {
                        return true;
                    }
                }
            }
        }
        false
    }
}

impl C {
    pub(in crate::kernel::equality_graph) fn bitvector_sides_for_congruence(
        &self,
    ) -> Option<(&T, &T)> {
        match self {
            Self::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: a,
                right: b,
            }
            | Self::Overflows {
                format: MachineIntegerType::Int32,
                op: OverflowOperation::Add,
                left: a,
                right: b,
            }
            | Self::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left: a,
                right: b,
            }
            | Self::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left: a,
                right: b,
            }
            | Self::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterThan,
                left: a,
                right: b,
            }
            | Self::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterEqual,
                left: a,
                right: b,
            }
            | Self::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left: a,
                right: b,
            }
            | Self::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::LessThan,
                left: a,
                right: b,
            }
            | Self::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::LessEqual,
                left: a,
                right: b,
            }
            | Self::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::GreaterThan,
                left: a,
                right: b,
            }
            | Self::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::GreaterEqual,
                left: a,
                right: b,
            }
            | Self::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::LessThan,
                left: a,
                right: b,
            }
            | Self::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::LessEqual,
                left: a,
                right: b,
            }
            | Self::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::GreaterThan,
                left: a,
                right: b,
            }
            | Self::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::GreaterEqual,
                left: a,
                right: b,
            } => Some((a, b)),
            _ => None,
        }
    }
}
