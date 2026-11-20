//! A call's variable arguments, as the value a variadic `extern` contract
//! reads.
//!
//! A C call to a function declared with `...` passes its arguments after the
//! named ones as one value, a `List<VarArg>`: one `VarArg` per argument,
//! after the default argument promotions (C11 6.5.2.2p6-7), first argument
//! first. `VarArg` is the `spec enum` of `library/c/stdarg.click`; the
//! contract names that list with its last parameter, `...args`
//! (docs/reference/language/c.md#variadic-calls).
//!
//! The kernel type built here is that `spec enum`'s: a kernel type's identity
//! is its name, arguments and variants, so this one and the surface's resolved
//! `List<VarArg>` are the same type.

use crate::kernel::{
    AlgebraicSchemas, AlgebraicType, AlgebraicValueType, AlgebraicVariantType, ProgramExpression,
    TypeParameterName,
};
use crate::languages::interface::InterfaceType;
use std::collections::BTreeMap;
use std::sync::Arc;

/// The name of the `spec enum` one variable argument is a value of.
pub(crate) const VARIABLE_ARGUMENT_TYPE: &str = "VarArg";

/// The library module that declares [`VARIABLE_ARGUMENT_TYPE`].
pub(crate) const STDARG_MODULE: &str = "library/c/stdarg.click";

/// The `VarArg` variant that holds an argument of each promoted type.
const VARIANTS: [(&str, InterfaceType); 4] = [
    ("Int", InterfaceType::Int32),
    ("UInt", InterfaceType::UInt32),
    (
        "Long",
        InterfaceType::Int64(crate::languages::c::syntax::LongRank::Long),
    ),
    (
        "ULong",
        InterfaceType::UInt64(crate::languages::c::syntax::LongRank::Long),
    ),
];

fn variable_argument_value_type() -> AlgebraicValueType {
    AlgebraicValueType::Algebraic {
        name: VARIABLE_ARGUMENT_TYPE.to_string(),
        arguments: Vec::new(),
    }
}

fn variable_argument_variants() -> Arc<[AlgebraicVariantType]> {
    VARIANTS
        .iter()
        .map(|(name, interface_type)| AlgebraicVariantType {
            name: (*name).to_string(),
            fields: vec![AlgebraicValueType::Program(interface_type.to_kernel_type())],
        })
        .collect()
}

fn schemas() -> (
    Arc<[AlgebraicVariantType]>,
    Arc<[AlgebraicVariantType]>,
    Arc<AlgebraicSchemas>,
) {
    let argument = variable_argument_value_type();
    let list = AlgebraicValueType::Algebraic {
        name: "List".to_string(),
        arguments: vec![argument.clone()],
    };
    let argument_variants = variable_argument_variants();
    let list_variants: Arc<[AlgebraicVariantType]> = vec![
        AlgebraicVariantType {
            name: "Nil".to_string(),
            fields: Vec::new(),
        },
        AlgebraicVariantType {
            name: "Cons".to_string(),
            fields: vec![argument.clone(), list.clone()],
        },
    ]
    .into();
    let schemas = AlgebraicSchemas::new(BTreeMap::from([
        (argument, argument_variants.clone()),
        (list, list_variants.clone()),
    ]));
    (argument_variants, list_variants, Arc::new(schemas))
}

/// The kernel type of one variable argument, `VarArg`.
pub(crate) fn variable_argument_type() -> TypeParameterName {
    static TYPE: std::sync::OnceLock<TypeParameterName> = std::sync::OnceLock::new();
    *TYPE.get_or_init(|| {
        let (variants, _, schemas) = schemas();
        TypeParameterName::of(&AlgebraicType {
            rigid: false,
            name: VARIABLE_ARGUMENT_TYPE.to_string(),
            arguments: Vec::new(),
            variants,
            schemas,
        })
    })
}

/// The kernel type of a call's variable arguments, `List<VarArg>`.
pub(crate) fn variable_arguments_type() -> TypeParameterName {
    static TYPE: std::sync::OnceLock<TypeParameterName> = std::sync::OnceLock::new();
    *TYPE.get_or_init(|| {
        let (_, variants, schemas) = schemas();
        TypeParameterName::of(&AlgebraicType {
            rigid: false,
            name: "List".to_string(),
            arguments: vec![variable_argument_value_type()],
            variants,
            schemas,
        })
    })
}

/// The `VarArg` variant that holds an argument of promoted type
/// `interface_type`, or `None` when Click does not model passing a value of
/// that type through `...`.
pub(crate) fn variant_for_promoted_type(interface_type: InterfaceType) -> Option<&'static str> {
    VARIANTS
        .iter()
        .find(|(_, held)| held.to_kernel_type() == interface_type.to_kernel_type())
        .map(|(name, _)| *name)
}

/// The list expression of `arguments`, each already promoted and paired with
/// its `VarArg` variant.
pub(crate) fn arguments_expression(
    arguments: impl DoubleEndedIterator<Item = (&'static str, ProgramExpression)>,
) -> ProgramExpression {
    arguments.rev().fold(
        ProgramExpression::EnumConstruct {
            enum_type: variable_arguments_type(),
            variant: "Nil".to_string(),
            fields: Vec::new(),
        },
        |tail, (variant, value)| ProgramExpression::EnumConstruct {
            enum_type: variable_arguments_type(),
            variant: "Cons".to_string(),
            fields: vec![
                ProgramExpression::EnumConstruct {
                    enum_type: variable_argument_type(),
                    variant: variant.to_string(),
                    fields: vec![value],
                },
                tail,
            ],
        },
    )
}
