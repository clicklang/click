//! Elaboration from declared types alone (`design/typed-surface.md`).
//!
//! Each test builds an `Elaborator` from declarations and a typing
//! environment over `NoOuterNames`, with no lowerer and no lowering context,
//! and checks the Surface it gives. The declarations still carry an empty
//! entry state, a kernel value, until they become a table of declared types.
use super::comparison_elaboration::LoweringQueries;
use super::typing_environment::NoOuterNames;
use super::*;
use crate::surface::typed_surface::{ArithmeticKind, ArithmeticOperator, ComparisonKind, LeafType};

/// Lowering's answers when it knows nothing: no pointer widths, no generic
/// call results, nothing refused. Right for any proposition without
/// pointers or generic calls.
struct NothingLowered;

impl LoweringQueries for NothingLowered {
    fn generic_call_returns_algebraic(&mut self, _: &SyntaxTerm) -> bool {
        false
    }
    fn refuse_untyped_pointer_access(&mut self, _: &SyntaxTerm) -> Result<(), String> {
        Ok(())
    }
    fn contract_pointer_element_width(&mut self, _: &SyntaxTerm) -> Option<u32> {
        None
    }
    fn call_pointer_element_width(&mut self, _: &SyntaxTerm) -> Result<Option<u32>, String> {
        Ok(None)
    }
}

/// Click binders with their declared types, and C parameters with theirs.
struct Declared {
    binders: Vec<(&'static str, ClickType)>,
    c_parameters: Vec<(&'static str, ProgramType)>,
}

impl Declared {
    fn elaborate<'s>(&self, proposition: &'s SyntaxProposition) -> SurfaceProposition<'s> {
        self.run(|elaborator, typing| {
            elaborator.elaborate_proposition(proposition, typing, &mut NothingLowered)
        })
    }

    fn elaborate_comparison(
        &self,
        left: SyntaxTerm,
        operator: ComparisonOperator,
        right: SyntaxTerm,
    ) -> Result<SurfaceProposition<'static>, String> {
        self.run(|elaborator, typing| {
            elaborator.elaborate_comparison(&left, operator, &right, typing, &mut NothingLowered)
        })
    }

    fn run<T>(&self, elaborate: impl FnOnce(&Elaborator<'_>, &TypingEnvironment<'_>) -> T) -> T {
        let entry_state = ExecutionState::new();
        let predicates = PredicateEnvironment::new(&[]);
        let functions = ClickFunctionEnvironment::new(&[]);
        let elaborator = Elaborator {
            declarations: Declarations {
                source_bindings: None,
                entry_state: &entry_state,
                result_type: ProgramType::Int32,
                entry_values: Default::default(),
                local_type_state: None,
                global_declarations: None,
                program_parameter_types: Arc::new(
                    self.c_parameters
                        .iter()
                        .map(|(name, ty)| (name.to_string(), *ty))
                        .collect(),
                ),
                pointer_element_types: Default::default(),
            },
            definitions: SpecDefinitions::new(&predicates, &functions),
            retained_states: None,
        };
        let mut typing = TypingEnvironment::in_scope(&NoOuterNames);
        for (name, declared) in &self.binders {
            typing.declare(*name, declared.clone());
        }
        elaborate(&elaborator, &typing)
    }
}

fn binder(name: &str) -> SyntaxTerm {
    SyntaxTerm::Binding(name.into())
}

fn c_variable(name: &str) -> SyntaxTerm {
    SyntaxTerm::ProgramExpression(ProgramExpression::Variable(name.into()))
}

fn literal(text: &str) -> SyntaxTerm {
    SyntaxTerm::IntegerLiteral(text.into())
}

fn integer_name(name: &str) -> SurfaceTerm {
    SurfaceTerm::Name {
        name: name.into(),
        ty: LeafType::Integer,
    }
}

fn program_literal(text: &str, ty: ProgramType) -> SurfaceTerm {
    SurfaceTerm::IntegerLiteral {
        text: text.into(),
        ty: LeafType::Program(ty),
    }
}

#[test]
fn integer_binders_elaborate_to_an_integer_comparison_of_integer_arithmetic() {
    let declared = Declared {
        binders: vec![("n", ClickType::Integer), ("m", ClickType::Integer)],
        c_parameters: vec![],
    };
    let surface = declared.elaborate_comparison(
        SyntaxTerm::Add(Box::new(binder("n")), Box::new(literal("1"))),
        ComparisonOperator::LessEqual,
        binder("m"),
    );
    assert_eq!(
        surface,
        Ok(SurfaceProposition::Comparison {
            kind: ComparisonKind::Integer,
            left: SurfaceTerm::Binary {
                op: ArithmeticOperator::Add,
                kind: ArithmeticKind::Integer,
                left: Box::new(integer_name("n")),
                right: Box::new(SurfaceTerm::IntegerLiteral {
                    text: "1".into(),
                    ty: LeafType::Integer,
                }),
            },
            operator: ComparisonOperator::LessEqual,
            right: integer_name("m"),
        })
    );
}

#[test]
fn c_parameters_elaborate_to_a_native_comparison_at_their_declared_types() {
    let declared = Declared {
        binders: vec![],
        c_parameters: vec![("x", ProgramType::Int32), ("y", ProgramType::Int64)],
    };
    let surface = declared.elaborate_comparison(
        SyntaxTerm::Multiply(Box::new(c_variable("x")), Box::new(literal("2"))),
        ComparisonOperator::Equal,
        literal("6"),
    );
    assert_eq!(
        surface,
        Ok(SurfaceProposition::Comparison {
            kind: ComparisonKind::Native,
            left: SurfaceTerm::Binary {
                op: ArithmeticOperator::Multiply,
                kind: ArithmeticKind::Native,
                left: Box::new(SurfaceTerm::Name {
                    name: "x".into(),
                    ty: LeafType::Program(ProgramType::Int32),
                }),
                right: Box::new(program_literal("2", ProgramType::Int32)),
            },
            operator: ComparisonOperator::Equal,
            right: program_literal("6", ProgramType::Int32),
        })
    );
    // C types an unsuffixed constant by its value: one past `int32` is an
    // `int64`.
    let surface = declared.elaborate_comparison(
        c_variable("y"),
        ComparisonOperator::LessThan,
        literal("3000000000"),
    );
    assert_eq!(
        surface,
        Ok(SurfaceProposition::Comparison {
            kind: ComparisonKind::Native,
            left: SurfaceTerm::Name {
                name: "y".into(),
                ty: LeafType::Program(ProgramType::Int64),
            },
            operator: ComparisonOperator::LessThan,
            right: program_literal("3000000000", ProgramType::Int64),
        })
    );
}

#[test]
fn an_integer_binder_compared_with_a_c_value_is_refused() {
    let declared = Declared {
        binders: vec![("n", ClickType::Integer)],
        c_parameters: vec![("x", ProgramType::Int32)],
    };
    assert_eq!(
        declared.elaborate_comparison(binder("n"), ComparisonOperator::Equal, c_variable("x")),
        Err("mathematical Integer expressions cannot be compared with C values".to_string())
    );
}

#[test]
fn algebraic_binders_elaborate_to_an_algebraic_equality_and_refuse_ordering() {
    let list = ClickType::Algebraic(AlgebraicTypeApplication::concrete("List"));
    let declared = Declared {
        binders: vec![("a", list.clone()), ("b", list)],
        c_parameters: vec![],
    };
    assert_eq!(
        declared.elaborate_comparison(binder("a"), ComparisonOperator::Equal, binder("b")),
        Ok(SurfaceProposition::Comparison {
            kind: ComparisonKind::Algebraic,
            left: SurfaceTerm::Untyped(binder("a")),
            operator: ComparisonOperator::Equal,
            right: SurfaceTerm::Untyped(binder("b")),
        })
    );
    assert_eq!(
        declared.elaborate_comparison(binder("a"), ComparisonOperator::LessThan, binder("b")),
        Err("algebraic values support only `==` and `!=` comparisons".to_string())
    );
}

#[test]
fn connectives_elaborate_around_each_comparison_and_a_refused_one_stays_untyped() {
    let declared = Declared {
        binders: vec![("n", ClickType::Integer)],
        c_parameters: vec![("x", ProgramType::Int32)],
    };
    let refused = SyntaxProposition::Comparison {
        left: binder("n"),
        operator: ComparisonOperator::Equal,
        right: c_variable("x"),
    };
    let proposition = SyntaxProposition::And(
        Box::new(SyntaxProposition::Comparison {
            left: binder("n"),
            operator: ComparisonOperator::GreaterThan,
            right: literal("0"),
        }),
        Box::new(SyntaxProposition::Not(Box::new(refused.clone()))),
    );
    let SurfaceProposition::And(left, right) = declared.elaborate(&proposition) else {
        panic!("a conjunction elaborates to a conjunction");
    };
    assert_eq!(
        *left,
        SurfaceProposition::Comparison {
            kind: ComparisonKind::Integer,
            left: integer_name("n"),
            operator: ComparisonOperator::GreaterThan,
            right: SurfaceTerm::IntegerLiteral {
                text: "0".into(),
                ty: LeafType::Integer,
            },
        }
    );
    // Lowering reaches the refused comparison and reports its error there.
    assert_eq!(
        *right,
        SurfaceProposition::Not(Box::new(SurfaceProposition::Untyped(&refused)))
    );
}
