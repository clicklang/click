//! Constructor type-argument inference.
//!
//! `List::Nil` and `List::Cons(x, xs)` leave out the type arguments of a
//! generic datatype. This pass fills them in during declaration expansion,
//! before validation, so every later pass and the kernel see the fully
//! applied `List<T>::Nil` a proof could have written. The arguments come
//! from one of two places: the constructor's own arguments (`Cons(node,
//! rb_inorder(t))` takes `T` from `rb_inorder`'s result), or the type its
//! position expects (a function's result, a call's parameter, the field of
//! an enclosing constructor, the other side of a comparison, or a typed
//! `let`). A constructor neither fixes is left as written, and validation
//! refuses it with the type arguments to write.
//!
//! The work is local: a constructor reads its direct arguments, and an
//! expected type is pushed only into the positions that are still
//! unapplied. Nothing here decides what a program means; an inferred type
//! is checked by validation and lowering exactly as a written one is.

use super::*;
use crate::surface::generics::{TypeSubstitution, unify_click_type};

/// The signature of a pure function, predicate or theorem, as inference
/// reads it.
struct Signature {
    type_parameters: Vec<String>,
    parameters: Vec<ClickType>,
    result: Option<ClickType>,
}

impl Signature {
    fn new(type_parameters: &[String], parameters: &[FunctionParameter]) -> Self {
        Self {
            type_parameters: type_parameters.to_vec(),
            parameters: parameters
                .iter()
                .map(FunctionParameter::click_type_with_object_class)
                .collect(),
            result: None,
        }
    }
}

/// Which signature table a call's name is read from.
#[derive(Clone, Copy)]
pub(super) enum CallKind {
    Function,
    Predicate,
    Theorem,
}

/// What inference reads: each datatype's definition, each signature, and
/// the types of the names in scope. `None` for a name marks a binder that
/// shadows an outer name with a type inference does not know.
pub(super) struct ConstructorTypes {
    datatypes: BTreeMap<String, AlgebraicTypeDefinition>,
    functions: BTreeMap<String, Signature>,
    predicates: BTreeMap<String, Signature>,
    theorems: BTreeMap<String, Signature>,
    variables: std::cell::RefCell<BTreeMap<String, Option<ClickType>>>,
    /// Whether any datatype takes type arguments; without one there is
    /// nothing to infer and every hook returns at once.
    active: bool,
}

impl ConstructorTypes {
    pub(super) fn new<'a>(
        datatypes: impl IntoIterator<Item = &'a AlgebraicTypeDefinition>,
        functions: impl IntoIterator<Item = &'a ClickFunctionDefinition>,
        predicates: impl IntoIterator<Item = &'a PredicateDefinition>,
        theorems: impl IntoIterator<Item = &'a TheoremDefinition>,
    ) -> Self {
        let datatypes = datatypes
            .into_iter()
            .map(|definition| (definition.name().to_string(), definition.clone()))
            .collect::<BTreeMap<_, _>>();
        let active = datatypes
            .values()
            .any(|definition| !definition.type_parameters().is_empty());
        if !active {
            return Self::inactive();
        }
        Self {
            datatypes,
            functions: functions
                .into_iter()
                .map(|definition| {
                    let mut signature =
                        Signature::new(definition.type_parameters(), definition.parameters());
                    signature.result = Some(
                        match (
                            definition.return_type().c_type(),
                            definition.return_object_class(),
                        ) {
                            (Some(c_type), Some(class)) => {
                                ClickType::from_object_pointer_class(c_type, class)
                            }
                            _ => definition.return_type().clone(),
                        },
                    );
                    (definition.name().to_string(), signature)
                })
                .collect(),
            predicates: predicates
                .into_iter()
                .map(|definition| {
                    (
                        definition.name().to_string(),
                        Signature::new(definition.type_parameters(), definition.parameters()),
                    )
                })
                .collect(),
            theorems: theorems
                .into_iter()
                .map(|definition| {
                    (
                        definition.name().to_string(),
                        Signature::new(definition.type_parameters(), definition.parameters()),
                    )
                })
                .collect(),
            variables: Default::default(),
            active,
        }
    }

    pub(super) fn inactive() -> Self {
        Self {
            datatypes: BTreeMap::new(),
            functions: BTreeMap::new(),
            predicates: BTreeMap::new(),
            theorems: BTreeMap::new(),
            variables: Default::default(),
            active: false,
        }
    }

    /// Begin a declaration whose parameters are `parameters`.
    pub(super) fn enter_declaration(
        &self,
        parameters: impl IntoIterator<Item = (String, ClickType)>,
    ) {
        if !self.active {
            return;
        }
        let mut variables = self.variables.borrow_mut();
        variables.clear();
        variables.extend(
            parameters
                .into_iter()
                .map(|(name, click_type)| (name, Some(click_type))),
        );
    }

    /// Bind `name` to `click_type` for a nested scope, returning what it
    /// replaced for [`Self::restore`].
    pub(super) fn bind(
        &self,
        name: &str,
        click_type: Option<ClickType>,
    ) -> Option<Option<ClickType>> {
        if !self.active {
            return None;
        }
        self.variables
            .borrow_mut()
            .insert(name.to_string(), click_type)
    }

    pub(super) fn restore(&self, name: &str, previous: Option<Option<ClickType>>) {
        if !self.active {
            return;
        }
        let mut variables = self.variables.borrow_mut();
        match previous {
            Some(previous) => {
                variables.insert(name.to_string(), previous);
            }
            None => {
                variables.remove(name);
            }
        }
    }

    /// Whether `application` names a generic datatype and leaves out its
    /// type arguments.
    fn unapplied(&self, application: &AlgebraicTypeApplication) -> bool {
        !application.rigid
            && application.arguments.is_empty()
            && self
                .datatypes
                .get(&application.name)
                .is_some_and(|definition| !definition.type_parameters().is_empty())
    }

    /// Whether `expression` still has an unapplied constructor in a
    /// position whose type is the expression's own.
    fn pending(&self, expression: &ContractExpression) -> bool {
        match expression {
            ContractExpression::AlgebraicConstructor { algebraic_type, .. } => {
                self.unapplied(algebraic_type)
            }
            ContractExpression::If {
                then_branch,
                else_branch,
                ..
            } => self.pending(then_branch) || self.pending(else_branch),
            ContractExpression::AlgebraicMatch { arms, .. } => {
                arms.iter().any(|arm| self.pending(&arm.body))
            }
            ContractExpression::Let { body, .. } => self.pending(body),
            ContractExpression::Old(inner)
            | ContractExpression::At {
                expression: inner, ..
            } => self.pending(inner),
            _ => false,
        }
    }

    /// The type `expression` has without looking at its surroundings, when
    /// inference can read it off directly.
    fn known_type(&self, expression: &ContractExpression) -> Option<ClickType> {
        match expression {
            ContractExpression::AlgebraicConstructor { algebraic_type, .. }
            | ContractExpression::AlgebraicVariable { algebraic_type, .. } => (!self
                .unapplied(algebraic_type))
            .then(|| ClickType::Algebraic(algebraic_type.clone())),
            ContractExpression::ResourceField(access) => access.click_type.clone(),
            ContractExpression::Binding(name)
            | ContractExpression::CBinding(name)
            | ContractExpression::CFragment(CExpression::Variable(name)) => {
                self.variables.borrow().get(name).cloned().flatten()
            }
            ContractExpression::Old(inner)
            | ContractExpression::At {
                expression: inner, ..
            } => self.known_type(inner),
            ContractExpression::If {
                then_branch,
                else_branch,
                ..
            } => self
                .known_type(then_branch)
                .or_else(|| self.known_type(else_branch)),
            ContractExpression::Call { name, arguments } => {
                let signature = self.functions.get(name)?;
                let result = signature.result.as_ref()?;
                if signature.type_parameters.is_empty() {
                    return Some(result.clone());
                }
                let substitution = self.call_substitution(signature, arguments);
                instantiate(result, &signature.type_parameters, &substitution)
            }
            _ => None,
        }
    }

    /// What the known argument types fix of a generic signature's type
    /// parameters. A conflict fixes nothing: validation reports it.
    fn call_substitution(
        &self,
        signature: &Signature,
        arguments: &[ContractExpression],
    ) -> TypeSubstitution {
        let allowed = signature
            .type_parameters
            .iter()
            .map(String::as_str)
            .collect::<BTreeSet<_>>();
        let mut substitution = TypeSubstitution::new();
        for (parameter, argument) in signature.parameters.iter().zip(arguments) {
            if let Some(actual) = self.known_type(argument)
                && unify_click_type(parameter, &actual, &allowed, &mut substitution).is_err()
            {
                return TypeSubstitution::new();
            }
        }
        substitution
    }

    /// Fill in an unapplied constructor's type arguments from its own
    /// arguments, then push field types into arguments that are still
    /// unapplied. Called once per constructor, after its arguments.
    pub(super) fn resolve_constructor(&self, expression: &mut ContractExpression) {
        if !self.active {
            return;
        }
        let ContractExpression::AlgebraicConstructor {
            algebraic_type,
            variant,
            arguments,
        } = expression
        else {
            return;
        };
        if self.unapplied(algebraic_type) {
            let Some(definition) = self.datatypes.get(&algebraic_type.name) else {
                return;
            };
            let Some(fields) = variant_fields(definition, variant, arguments.len()) else {
                return;
            };
            let parameters = definition.type_parameters();
            let pattern = AlgebraicTypeApplication {
                rigid: false,
                name: algebraic_type.name.clone(),
                arguments: parameters
                    .iter()
                    .map(|parameter| ClickType::Parameter(parameter.clone()))
                    .collect(),
            };
            let allowed = parameters
                .iter()
                .map(String::as_str)
                .collect::<BTreeSet<_>>();
            let mut substitution = TypeSubstitution::new();
            for (field, argument) in fields.iter().zip(arguments.iter()) {
                let (Ok(field), Some(actual)) = (
                    instantiate_field_type(definition, &pattern, field),
                    self.known_type(argument),
                ) else {
                    continue;
                };
                if unify_click_type(&field, &actual, &allowed, &mut substitution).is_err() {
                    return;
                }
            }
            let Some(inferred) = parameters
                .iter()
                .map(|parameter| substitution.get(parameter).cloned())
                .collect::<Option<Vec<_>>>()
            else {
                return;
            };
            algebraic_type.arguments = inferred;
        }
        self.push_into_fields(algebraic_type, variant, arguments);
    }

    fn push_into_fields(
        &self,
        application: &AlgebraicTypeApplication,
        variant: &str,
        arguments: &mut [ContractExpression],
    ) {
        if !arguments.iter().any(|argument| self.pending(argument)) {
            return;
        }
        let Some(definition) = self.datatypes.get(&application.name) else {
            return;
        };
        let Some(fields) = variant_fields(definition, variant, arguments.len()) else {
            return;
        };
        for (field, argument) in fields.iter().zip(arguments.iter_mut()) {
            if self.pending(argument)
                && let Ok(expected) = instantiate_field_type(definition, application, field)
            {
                self.push_expected(argument, &expected);
            }
        }
    }

    /// Give the unapplied constructors in `expression`'s own result
    /// positions the type `expected`.
    pub(super) fn push_expected(&self, expression: &mut ContractExpression, expected: &ClickType) {
        if !self.active {
            return;
        }
        let ClickType::Algebraic(expected_application) = expected else {
            return;
        };
        match expression {
            ContractExpression::AlgebraicConstructor {
                algebraic_type,
                variant,
                arguments,
            } => {
                if self.unapplied(algebraic_type) {
                    let arity = self
                        .datatypes
                        .get(&algebraic_type.name)
                        .map_or(0, |definition| definition.type_parameters().len());
                    if expected_application.rigid
                        || expected_application.name != algebraic_type.name
                        || expected_application.arguments.len() != arity
                    {
                        return;
                    }
                    algebraic_type
                        .arguments
                        .clone_from(&expected_application.arguments);
                }
                self.push_into_fields(algebraic_type, variant, arguments);
            }
            ContractExpression::If {
                then_branch,
                else_branch,
                ..
            } => {
                self.push_expected(then_branch, expected);
                self.push_expected(else_branch, expected);
            }
            ContractExpression::AlgebraicMatch { arms, .. } => {
                for arm in arms {
                    self.push_expected(&mut arm.body, expected);
                }
            }
            ContractExpression::Let { body, .. } => self.push_expected(body, expected),
            ContractExpression::Old(inner)
            | ContractExpression::At {
                expression: inner, ..
            } => self.push_expected(inner, expected),
            _ => {}
        }
    }

    /// Push each parameter type of `name`'s signature into the call
    /// arguments still unapplied, once the other arguments fix it.
    pub(super) fn resolve_call(
        &self,
        kind: CallKind,
        name: &str,
        arguments: &mut [ContractExpression],
    ) {
        if !self.active || !arguments.iter().any(|argument| self.pending(argument)) {
            return;
        }
        let table = match kind {
            CallKind::Function => &self.functions,
            CallKind::Predicate => &self.predicates,
            CallKind::Theorem => &self.theorems,
        };
        let Some(signature) = table.get(name) else {
            return;
        };
        let substitution = if signature.type_parameters.is_empty() {
            TypeSubstitution::new()
        } else {
            self.call_substitution(signature, arguments)
        };
        for (parameter, argument) in signature.parameters.iter().zip(arguments.iter_mut()) {
            if self.pending(argument)
                && let Some(expected) =
                    instantiate(parameter, &signature.type_parameters, &substitution)
            {
                self.push_expected(argument, &expected);
            }
        }
    }

    /// An unapplied side of a comparison takes the other side's type.
    pub(super) fn resolve_comparison(
        &self,
        left: &mut ContractExpression,
        right: &mut ContractExpression,
    ) {
        if !self.active {
            return;
        }
        if self.pending(left) {
            if let Some(expected) = self.known_type(right) {
                self.push_expected(left, &expected);
            }
        } else if self.pending(right)
            && let Some(expected) = self.known_type(left)
        {
            self.push_expected(right, &expected);
        }
    }

    /// The types of a match arm's bindings, when the scrutinee's type is
    /// known; an unknown binding shadows whatever the name meant outside.
    pub(super) fn arm_binding_types(
        &self,
        scrutinee: &ContractExpression,
        arm: &AlgebraicMatchArm,
    ) -> Vec<Option<ClickType>> {
        let scrutinee = if self.active {
            self.known_type(scrutinee)
        } else {
            None
        };
        self.variant_binding_types(scrutinee.as_ref(), &arm.variant, arm.bindings.len())
    }

    /// The types of a proof `match` or `induct` arm's bindings.
    pub(super) fn proof_arm_binding_types(
        &self,
        scrutinee: Option<&ClickType>,
        arm: &ProofInductionArm,
    ) -> Vec<Option<ClickType>> {
        self.variant_binding_types(scrutinee, &arm.variant, arm.bindings.len())
    }

    /// The type of the scrutinee of a proof `match`.
    pub(super) fn scrutinee_type(&self, scrutinee: &ContractExpression) -> Option<ClickType> {
        if !self.active {
            return None;
        }
        self.known_type(scrutinee)
    }

    /// The type of the name `name` in scope, for `induct(name)`.
    pub(super) fn variable_type(&self, name: &str) -> Option<ClickType> {
        if !self.active {
            return None;
        }
        self.variables.borrow().get(name).cloned().flatten()
    }

    fn variant_binding_types(
        &self,
        scrutinee: Option<&ClickType>,
        variant: &str,
        arity: usize,
    ) -> Vec<Option<ClickType>> {
        let unknown = || vec![None; arity];
        let Some(ClickType::Algebraic(application)) = scrutinee else {
            return unknown();
        };
        let Some(definition) = self.datatypes.get(&application.name) else {
            return unknown();
        };
        let Some(fields) = variant_fields(definition, variant, arity) else {
            return unknown();
        };
        fields
            .iter()
            .map(|field| instantiate_field_type(definition, application, field).ok())
            .collect()
    }

    /// Bind each of `names` to its type for the scope `body` expands,
    /// then restore what the names meant outside.
    pub(super) fn with_bindings<T>(
        &self,
        names: &[String],
        types: Vec<Option<ClickType>>,
        body: impl FnOnce() -> T,
    ) -> T {
        let previous = names
            .iter()
            .zip(types)
            .map(|(name, click_type)| self.bind(name, click_type))
            .collect::<Vec<_>>();
        let result = body();
        for (name, previous) in names.iter().zip(previous).rev() {
            self.restore(name, previous);
        }
        result
    }

    /// The type of `expression` for a `let` binding it initializes.
    pub(super) fn binding_type(&self, expression: &ContractExpression) -> Option<ClickType> {
        if !self.active {
            return None;
        }
        self.known_type(expression)
    }
}

fn variant_fields<'a>(
    definition: &'a AlgebraicTypeDefinition,
    variant: &str,
    arity: usize,
) -> Option<&'a [AlgebraicFieldType]> {
    definition
        .variants()
        .iter()
        .find(|candidate| candidate.name() == variant)
        .map(AlgebraicVariantDefinition::fields)
        .filter(|fields| fields.len() == arity)
}

/// `click_type` with the signature's own type parameters replaced, or
/// `None` while one of them is still unknown. Any other type parameter is
/// the enclosing declaration's own and stays as it is.
fn instantiate(
    click_type: &ClickType,
    parameters: &[String],
    substitution: &TypeSubstitution,
) -> Option<ClickType> {
    match click_type {
        ClickType::Parameter(name) if parameters.contains(name) => substitution.get(name).cloned(),
        ClickType::Algebraic(application) => Some(ClickType::Algebraic(AlgebraicTypeApplication {
            rigid: application.rigid,
            name: application.name.clone(),
            arguments: application
                .arguments
                .iter()
                .map(|argument| instantiate(argument, parameters, substitution))
                .collect::<Option<Vec<_>>>()?,
        })),
        other => Some(other.clone()),
    }
}

/// The refusal for a constructor whose type arguments nothing fixed.
pub(in crate::surface) fn unapplied_constructor_message(
    datatype: &str,
    variant: &str,
    type_parameters: &[String],
) -> String {
    let parameters = type_parameters.join(", ");
    format!(
        "cannot infer the type arguments of `{datatype}::{variant}`: neither its arguments nor the type its position expects fix `{parameters}`; write them, as in `{datatype}<...>::{variant}`"
    )
}
