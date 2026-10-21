//! C++ class object state in a sidecar, written by rewriting the sidecar's
//! tokens before it is parsed, as a Rust trait's object state is.
//!
//! A polymorphic class may declare model functions of its object,
//! `class Shape { function size(this) -> int32; }`, and each class passed as
//! one defines them, `class Square : Shape { function size(this) -> int32 {
//! this->side } }`. The class's object is then a sealed abstract resource
//! whose fields are those functions, `Shape__object`:
//!
//! - A method of the class, and a parameter `Shape& x`, holds the object:
//!   its contract owns `__object_this: Shape__object(this)` or `__object_x:
//!   Shape__object(&x)` and reads `size(x)` as its field `size`. A `const`
//!   method or reference keeps the fields; a mutable one may change them,
//!   which its `ensures` read as new and `old(size(x))` as at entry.
//! - A method of a defining class is verified on its object's memory: it owns
//!   `*this`, `size(this)` is the class's definition, and an override of the
//!   object class's method inherits that method's clauses read the same way.
//!   Its `requires` must follow from them, which the `contract` named for it
//!   with `_iface` states, and which verification checks.
//! - The importer places the class's trusted pack and unpack where a
//!   reference to it becomes a reference to the object class; their
//!   contracts carry the definitions.
//!
//! Every other token is kept, with its position.

use super::rust_trait_objects::{
    Spanned, at, error_at, field_read, handle, ident, is_ident, matching, rename, rewrite_calls,
    same_tokens, split_clauses,
};
use super::*;

/// A class whose object carries state.
struct ObjectClass {
    family: String,
    /// The type arguments a use names the family at, `Holder__object<int>`:
    /// none for a class that is not a template's.
    arguments: Vec<String>,
    /// The type parameters of the resource this block declares, none for a
    /// class that is not generic; `None` for an instance of a generic block,
    /// which declares it.
    declares: Option<Vec<String>>,
    functions: Vec<(String, Vec<Spanned>)>,
    methods: BTreeMap<String, Interface>,
}

/// An object class method's interface, as its sidecar contract writes it.
#[derive(Clone)]
struct Interface {
    parameters: Vec<String>,
    clauses: Vec<Vec<Spanned>>,
}

/// A class that defines an object class's functions on its own memory.
struct DefiningClass {
    root: String,
    /// The class its block names as its base: the object class, or a
    /// defining class whose definitions it inherits through its base part.
    base: String,
    definitions: BTreeMap<String, Vec<Spanned>>,
    /// Where its `class` block names it.
    position: SourcePosition,
    /// Whether it is a generic block, `template<class T> class Wrap<T>`,
    /// whose methods are verified once for every type: its instances are
    /// what references convert from.
    generic: bool,
}

/// A `class` block as written, before its base is resolved.
struct WrittenClass {
    base: Option<String>,
    declared: Vec<(String, Vec<Spanned>)>,
    defined: BTreeMap<String, Vec<Spanned>>,
    position: SourcePosition,
    /// The type parameters of a generic block, `template<class T>`.
    parameters: Option<Vec<String>>,
}

/// A function contract at the top level of the sidecar.
struct Head {
    /// The item's first token, after an `extern` or `contract` keyword.
    start: usize,
    /// A generic method's `template<...>` list, which its other contracts
    /// repeat.
    template: Vec<Spanned>,
    /// Its return type's tokens.
    result: Vec<Spanned>,
    class: Option<String>,
    method: String,
    list_open: usize,
    list_close: usize,
    is_const: bool,
    body_open: usize,
    body_close: usize,
    /// The index after the item, its proof included.
    end: usize,
}

/// The importer name of `class`'s method `method`, `Square::area`.
fn method_name(class: &str, method: &str) -> String {
    crate::languages::cpp::names::path_name(&[class, method])
}

/// The name of the abstract resource that is class `class`'s object. A
/// class template's instance, `Holder<int>`, has the generic resource of its
/// template, `Holder__object`, at its arguments.
fn object_family(class: &str) -> String {
    let template = class.split_once('<').map_or(class, |(name, _)| name);
    format!("{template}__object")
}

/// The type arguments of a class template instance's spelling, `["int"]` for
/// `Holder<int>`, as Clang prints them; none for a class that is not a
/// template's.
fn spelled_arguments(class: &str) -> Vec<String> {
    match class.split_once('<') {
        Some((_, rest)) => rest
            .trim_end_matches('>')
            .split(", ")
            .map(str::to_string)
            .collect(),
        None => Vec::new(),
    }
}

/// The class at `start`, `Shape` or a class template's instance
/// `Holder<int>`, spelled as Clang prints it, and the index after it.
fn class_at(source: &[Spanned], start: usize) -> Option<(String, usize)> {
    let Some((Token::Ident(name), _)) = source.get(start) else {
        return None;
    };
    if source.get(start + 1).map(|(token, _)| token) != Some(&Token::LessThan) {
        return Some((name.clone(), start + 1));
    }
    let plain = source[start + 1..]
        .iter()
        .map(|(token, _)| token.clone())
        .collect::<Vec<_>>();
    let (arguments, end) = super::cpp_syntax::template_arguments_at(&plain, 0, true)?;
    Some((format!("{name}{arguments}"), start + 1 + end))
}

/// `tokens` with each of `substitution`'s type parameters spelled as its
/// argument, `unsigned int` as two words.
fn substituted(tokens: &[Spanned], substitution: &BTreeMap<String, String>) -> Vec<Spanned> {
    let mut output = Vec::with_capacity(tokens.len());
    for (token, position) in tokens {
        match token {
            Token::Ident(word) if substitution.contains_key(word) => {
                for part in substitution[word].split_whitespace() {
                    output.push((ident(part), position.clone()));
                }
            }
            token => output.push((token.clone(), position.clone())),
        }
    }
    output
}

/// A use of `object`'s resource, `Holder__object<int>`, before its `(`.
fn family_use(object: &ObjectClass, position: &SourcePosition) -> Vec<Spanned> {
    let mut tokens = vec![(ident(&object.family), position.clone())];
    if !object.arguments.is_empty() {
        tokens.push((Token::LessThan, position.clone()));
        for (index, argument) in object.arguments.iter().enumerate() {
            if index > 0 {
                tokens.push((Token::Comma, position.clone()));
            }
            for part in argument.split_whitespace() {
                tokens.push((ident(part), position.clone()));
            }
        }
        tokens.push((Token::GreaterThan, position.clone()));
    }
    tokens
}

/// The layout name of the record class `class` spells: a class template's
/// instance, `Holder<int>`, is the record the import names for it.
fn record_of(class: &str, records: &BTreeMap<String, String>) -> String {
    records
        .get(class)
        .cloned()
        .unwrap_or_else(|| class.to_string())
}

/// The `template<...>` parameter list at `start`, with the index after it.
fn template_prefix(source: &[Spanned], start: usize) -> Option<(Vec<String>, usize)> {
    if !is_ident(source.get(start), "template")
        || source.get(start + 1).map(|(token, _)| token) != Some(&Token::LessThan)
    {
        return None;
    }
    let close = matching(source, start + 1)?;
    let names = super::cpp_generic_templates::template_parameters(source, start + 1, close)?;
    Some((names, close + 1))
}

/// The `contract` that states a defining class's method's interface on its
/// own memory, which the method must refine. `implementation` is the
/// method's importer name.
fn implementation_interface_contract(implementation: &str) -> String {
    super::rust_trait_objects::implementation_interface_contract(implementation)
}

/// The methods a rewrite states on objects, by importer name.
#[derive(Default)]
pub(super) struct ObjectMethods {
    /// The object classes' methods: an override of one inherits no clauses,
    /// being stated on its own memory.
    pub(super) interfaces: BTreeSet<String>,
    /// The defining classes' methods, which are so stated.
    pub(super) on_memory: BTreeSet<String>,
    /// The defining classes.
    pub(super) defining: BTreeSet<String>,
    /// The dispatches the rewrite states on the object, by name: the class
    /// another derives from and its method.
    pub(super) dispatches: BTreeMap<String, (String, String)>,
    /// For each defining class another derives from, the object class, and
    /// a class deriving from it.
    pub(super) derived_from: BTreeMap<String, (String, String)>,
    /// Each function's parameters that are references to such a class, and
    /// hold the object, by importer name: the parameter and its class.
    pub(super) object_parameters: BTreeMap<String, BTreeMap<String, String>>,
}

/// Rewrites the class object state of a C++ sidecar, and returns the
/// methods it states on objects.
pub(super) fn rewrite_class_objects(
    tokens: Vec<Token>,
    positions: Vec<SourcePosition>,
    records: &BTreeMap<String, String>,
) -> Result<(Vec<Token>, Vec<SourcePosition>, ObjectMethods), ClickError> {
    let source: Vec<Spanned> = tokens.into_iter().zip(positions).collect();
    let (mut objects, defining) = classes(&source, records)?;
    if objects.is_empty() {
        let (tokens, positions) = source.into_iter().unzip();
        return Ok((tokens, positions, ObjectMethods::default()));
    }
    let found = heads(&source);
    // A reference to the object class, or to a defining class another
    // derives from, holds the object of whichever class it refers to.
    let derived_from = defining
        .values()
        .filter(|definer| defining.contains_key(&definer.base))
        .map(|definer| definer.base.clone())
        .collect::<BTreeSet<_>>();
    let mut references = objects
        .keys()
        .map(|class| (class.clone(), class.clone()))
        .collect::<BTreeMap<_, _>>();
    for class in &derived_from {
        references.insert(class.clone(), defining[class].root.clone());
    }
    for head in &found {
        if let Some(class) = &head.class
            && let Some(object) = objects.get_mut(class)
        {
            object.methods.insert(
                head.method.clone(),
                Interface {
                    parameters: parameters(&source[head.list_open + 1..head.list_close])
                        .into_iter()
                        .map(|parameter| parameter.name)
                        .collect(),
                    clauses: split_clauses(&source[head.body_open + 1..head.body_close]),
                },
            );
        }
    }
    // An instance of a generic block has the block's methods, which are
    // written out at it.
    let generic_methods = objects
        .iter()
        .filter(|(_, object)| {
            object
                .declares
                .as_ref()
                .is_some_and(|names| !names.is_empty())
        })
        .map(|(class, object)| {
            (
                object.family.clone(),
                (class.clone(), object.methods.clone()),
            )
        })
        .collect::<BTreeMap<_, _>>();
    for object in objects.values_mut() {
        if object.declares.is_none()
            && let Some((_, methods)) = generic_methods.get(&object.family)
        {
            object.methods = methods.clone();
        }
    }
    // A class deriving from a defining class that inherits a method stated
    // on an ancestor's memory runs it on its own object, which the method's
    // proof reads by that ancestor's definitions: each function the object
    // class's interface for it reads is the same here, read through the
    // base parts.
    let stated = found
        .iter()
        .filter_map(|head| Some((head.class.as_deref()?, head.method.as_str())))
        .collect::<BTreeSet<_>>();
    for (class, definer) in &defining {
        let root = &objects[&definer.root];
        for (method, interface) in &root.methods {
            if stated.contains(&(class.as_str(), method.as_str())) {
                continue;
            }
            let mut ancestor = &definer.base;
            let mut depth = 1;
            while let Some(parent) = defining.get(ancestor) {
                if !stated.contains(&(ancestor.as_str(), method.as_str())) {
                    ancestor = &parent.base;
                    depth += 1;
                    continue;
                }
                for (function, _) in &root.functions {
                    let read = interface.clauses.iter().any(|clause| {
                        clause.windows(2).any(|pair| {
                            is_ident(pair.first(), function) && pair[1].0 == Token::LParen
                        })
                    });
                    let inherited = (0..depth)
                        .try_fold(parent.definitions[function].clone(), |definition, _| {
                            through_base(&definition)
                        });
                    if read
                        && !inherited.is_some_and(|inherited| {
                            same_tokens(&inherited, &definer.definitions[function])
                        })
                    {
                        return Err(error_at(
                            &definer.position,
                            format!(
                                "`{class}` inherits `{ancestor}::{method}`, whose interface \
                                 reads `{function}`, which `{class}` defines otherwise than \
                                 `{ancestor}`: `{ancestor}::{method}` is stated on \
                                 `{ancestor}`'s definitions, so `{class}` overrides it, \
                                 `{class}::{method}`"
                            ),
                        ));
                    }
                }
                break;
            }
        }
    }
    // The dispatches stated on the object, and the parameters holding the
    // object of a class another derives from.
    let mut dispatches = BTreeMap::new();
    let mut object_parameters = BTreeMap::<String, BTreeMap<String, String>>::new();
    for head in &found {
        let own = parameters(&source[head.list_open + 1..head.list_close]);
        if let Some(class) = head
            .class
            .as_ref()
            .filter(|class| derived_from.contains(*class))
            && objects[&defining[class].root]
                .methods
                .get(&head.method)
                .is_some_and(|interface| interface.parameters.len() == own.len())
        {
            dispatches.insert(
                crate::languages::cpp::names::object_dispatch_name(class, &head.method),
                (class.clone(), head.method.clone()),
            );
        }
        let function = match &head.class {
            Some(class) => method_name(class, &head.method),
            None => crate::languages::cpp::names::path_name(&[head.method.as_str()]),
        };
        for parameter in &own {
            let Some((_, class)) = referenced_class(parameter) else {
                continue;
            };
            if derived_from.contains(&class) {
                object_parameters
                    .entry(function.clone())
                    .or_default()
                    .insert(parameter.name.clone(), class);
            }
        }
    }
    let mut output = Vec::with_capacity(source.len());
    // A generic block's methods stand for its instances' too.
    let mut on_memory = BTreeSet::new();
    for head in &found {
        let Some(class) = head.class.as_ref() else {
            continue;
        };
        let Some(definer) = defining.get(class) else {
            continue;
        };
        on_memory.insert(method_name(class, &head.method));
        if definer.generic {
            let template = class.split_once('<').map(|(name, _)| name);
            for (instance, instance_definer) in &defining {
                if !instance_definer.generic
                    && instance.split_once('<').map(|(name, _)| name) == template
                {
                    on_memory.insert(method_name(instance, &head.method));
                }
            }
        }
    }
    let mut pending = found.iter().peekable();
    let mut index = 0;
    let mut depth = 0i32;
    while index < source.len() {
        if let Some(head) = pending.next_if(|head| head.start == index) {
            rewrite_function(
                &source,
                head,
                &objects,
                &defining,
                &references,
                records,
                &mut output,
            )?;
            index = head.end;
            continue;
        }
        if depth == 0
            && let Some((_, class_start)) = class_block_at(&source, index)
            && let Some((class, _)) = class_at(&source, class_start + 1)
            && let Some(open) =
                (class_start + 2..source.len()).find(|&at| source[at].0 == Token::LBrace)
            && let Some(close) = matching(&source, open)
        {
            let position = &source[class_start + 1].1;
            // A generic block stands for its template's instances too, which
            // no block writes.
            let template = class.split_once('<').map(|(name, _)| name);
            let instances = objects
                .keys()
                .chain(defining.keys())
                .filter(|instance| {
                    **instance != class
                        && template.is_some()
                        && instance.split_once('<').map(|(name, _)| name) == template
                        && (objects
                            .get(&class)
                            .is_some_and(|object| object.declares.is_some())
                            || defining.get(&class).is_some_and(|definer| definer.generic))
                })
                .cloned()
                .collect::<BTreeSet<_>>();
            for class in std::iter::once(&class).chain(&instances) {
                if let Some(object) = objects.get(class) {
                    output.extend(object_declaration(object, position));
                } else if let Some(definer) = defining.get(class)
                    && !definer.generic
                {
                    let object = &objects[&definer.root];
                    // The class becomes the object of the object class, and of
                    // each defining class it derives from, and of itself where a
                    // class derives from it.
                    let mut targets = vec![definer.root.clone()];
                    let mut ancestor = &definer.base;
                    while let Some(parent) = defining.get(ancestor) {
                        targets.push(ancestor.clone());
                        ancestor = &parent.base;
                    }
                    if derived_from.contains(class) {
                        targets.push(class.clone());
                        output.extend(dispatch_contracts(
                            &source,
                            &found,
                            class,
                            definer,
                            &objects,
                            &defining,
                            &references,
                            records,
                        )?);
                    }
                    for target in &targets {
                        output.extend(coercion_contracts(
                            class, target, definer, object, records, position,
                        ));
                    }
                }
            }
            index = close + 1;
            continue;
        }
        match source[index].0 {
            Token::LBrace | Token::LParen | Token::LBracket => depth += 1,
            Token::RBrace | Token::RParen | Token::RBracket => depth -= 1,
            _ => {}
        }
        output.push(source[index].clone());
        index += 1;
    }
    let interfaces = objects
        .iter()
        .flat_map(|(class, object)| {
            object
                .methods
                .keys()
                .map(move |method| method_name(class, method))
        })
        .collect();
    let (tokens, positions) = output.into_iter().unzip();
    Ok((
        tokens,
        positions,
        ObjectMethods {
            interfaces,
            on_memory,
            defining: defining.keys().cloned().collect(),
            dispatches,
            derived_from: derived_from
                .iter()
                .map(|class| {
                    let derived = defining
                        .iter()
                        .find(|(_, definer)| &definer.base == class)
                        .map(|(derived, _)| derived.clone())
                        .unwrap_or_default();
                    (class.clone(), (defining[class].root.clone(), derived))
                })
                .collect(),
            object_parameters,
        },
    ))
}

/// The `class` blocks: those that declare their object's functions, and
/// those that define them after naming a base. A generic block,
/// `template<class T> class Holder<T> { ... }`, is also written out at each
/// instance of its template that `records` names, `Holder<int>`.
fn classes(
    source: &[Spanned],
    records: &BTreeMap<String, String>,
) -> Result<
    (
        BTreeMap<String, ObjectClass>,
        BTreeMap<String, DefiningClass>,
    ),
    ClickError,
> {
    let mut written = BTreeMap::new();
    let mut depth = 0i32;
    let mut index = 0;
    while index < source.len() {
        if depth == 0
            && let Some((parameters, class_start)) = class_block_at(source, index)
        {
            let position = source[class_start].1.clone();
            let shape = || {
                error_at(
                    &position,
                    "a `class` block is written `class Name { ... }` or `class Name : Base { ... }`, \
                     a generic one `template<class T> class Name<T> { ... }`",
                )
            };
            let (class, after) = class_at(source, class_start + 1).ok_or_else(shape)?;
            if let Some(parameters) = &parameters
                && spelled_arguments(&class) != *parameters
            {
                return Err(error_at(
                    &position,
                    format!(
                        "a generic `class` block names its template at its own parameters, \
                         `class {}<{}>`",
                        class
                            .split_once('<')
                            .map_or(class.as_str(), |(name, _)| name),
                        parameters.join(", ")
                    ),
                ));
            }
            let (base, open) = match source.get(after).map(|(token, _)| token) {
                Some(Token::Colon) => match class_at(source, after + 1) {
                    Some((base, open)) => (Some(base), open),
                    None => (None, after + 1),
                },
                _ => (None, after),
            };
            if source.get(open).map(|(token, _)| token) != Some(&Token::LBrace) {
                return Err(shape());
            }
            let close = matching(source, open)
                .ok_or_else(|| error_at(&position, "unterminated `class` block"))?;
            let mut declared = Vec::new();
            let mut defined = BTreeMap::new();
            let mut item = open + 1;
            while item < close {
                let shape = || {
                    error_at(
                        &source[item].1,
                        "a class `function` is written `function name(this) -> T;`, or with its \
                         definition, `function name(this) -> T { ... }`",
                    )
                };
                if !is_ident(source.get(item), "function") {
                    return Err(shape());
                }
                let (Some((Token::Ident(function), _)), Some((Token::LParen, _))) =
                    (source.get(item + 1), source.get(item + 2))
                else {
                    return Err(shape());
                };
                if !is_ident(source.get(item + 3), "this")
                    || source.get(item + 4).map(|(token, _)| token) != Some(&Token::RParen)
                    || source.get(item + 5).map(|(token, _)| token) != Some(&Token::Arrow)
                {
                    return Err(shape());
                }
                let end = (item + 6..close)
                    .find(|&at| matches!(source[at].0, Token::Semicolon | Token::LBrace))
                    .ok_or_else(shape)?;
                let result = source[item + 6..end].to_vec();
                if source[end].0 == Token::Semicolon {
                    declared.push((function.clone(), result));
                    item = end + 1;
                } else {
                    let body_close = matching(source, end).ok_or_else(shape)?;
                    defined.insert(function.clone(), source[end + 1..body_close].to_vec());
                    item = body_close + 1;
                }
            }
            written.insert(
                class,
                WrittenClass {
                    base,
                    declared,
                    defined,
                    position,
                    parameters,
                },
            );
            index = close + 1;
            continue;
        }
        match source[index].0 {
            Token::LBrace | Token::LParen | Token::LBracket => depth += 1,
            Token::RBrace | Token::RParen | Token::RBracket => depth -= 1,
            _ => {}
        }
        index += 1;
    }
    // Each instance of a generic block's template the import names is the
    // block with its type arguments for its parameters.
    let mut instances = Vec::new();
    for (class, block) in &written {
        let Some(parameters) = &block.parameters else {
            continue;
        };
        let template = class
            .split_once('<')
            .map_or(class.as_str(), |(name, _)| name);
        for spelling in records.keys() {
            let arguments = spelled_arguments(spelling);
            if spelling == class
                || written.contains_key(spelling)
                || spelling.split_once('<').map(|(name, _)| name) != Some(template)
                || arguments.len() != parameters.len()
            {
                continue;
            }
            let substitution = parameters
                .iter()
                .cloned()
                .zip(arguments.iter().cloned())
                .collect::<BTreeMap<_, _>>();
            // The base at the instance's arguments, `Holder<int>` for
            // `Holder<T>`.
            let base = block.base.as_ref().map(|base| match base.split_once('<') {
                Some((name, _)) => format!(
                    "{name}<{}>",
                    spelled_arguments(base)
                        .iter()
                        .map(|argument| substitution.get(argument).unwrap_or(argument).clone())
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
                None => base.clone(),
            });
            instances.push((
                spelling.clone(),
                WrittenClass {
                    base,
                    declared: block
                        .declared
                        .iter()
                        .map(|(function, result)| {
                            (function.clone(), substituted(result, &substitution))
                        })
                        .collect(),
                    defined: block
                        .defined
                        .iter()
                        .map(|(function, definition)| {
                            (function.clone(), substituted(definition, &substitution))
                        })
                        .collect(),
                    position: block.position.clone(),
                    parameters: None,
                },
            ));
        }
    }
    let generic_blocks = written
        .iter()
        .filter(|(_, block)| block.parameters.is_some())
        .map(|(class, _)| class.clone())
        .collect::<BTreeSet<_>>();
    written.extend(instances);
    let mut objects = BTreeMap::new();
    // Each defining class's base and own definitions, before its root is known.
    let mut bases = BTreeMap::new();
    for (class, block) in written {
        match (
            block.base,
            block.declared.is_empty(),
            block.defined.is_empty(),
        ) {
            (None, false, true) => {
                let arguments = spelled_arguments(&class);
                objects.insert(
                    class.clone(),
                    ObjectClass {
                        family: object_family(&class),
                        declares: match &block.parameters {
                            Some(parameters) => Some(parameters.clone()),
                            None if arguments.is_empty() => Some(Vec::new()),
                            None => None,
                        },
                        arguments,
                        functions: block.declared,
                        methods: BTreeMap::new(),
                    },
                );
            }
            (Some(base), true, _) => {
                bases.insert(class, (base, block.defined, block.position));
            }
            _ => {
                return Err(error_at(
                    &block.position,
                    "a `class` block either declares its object's functions, \
                     `class Shape { function size(this) -> int32; }`, or names its base and \
                     defines them, `class Square : Shape { function size(this) -> int32 { \
                     this->side } }`",
                ));
            }
        }
    }
    // Each class defines the functions on its own memory. Its base is the
    // class whose object it is, or a defining class, whose definitions it
    // inherits read through its base part unless it writes its own. A base
    // is resolved before the classes deriving from it.
    let mut defining: BTreeMap<String, DefiningClass> = BTreeMap::new();
    let mut pending = bases.keys().collect::<Vec<_>>();
    while !pending.is_empty() {
        let before = pending.len();
        let mut deferred = Vec::new();
        for class in pending {
            let (base, definitions, position) = &bases[class];
            let (root, inherited) = if objects.contains_key(base) {
                (base.clone(), None)
            } else if let Some(parent) = defining.get(base) {
                (parent.root.clone(), Some(parent))
            } else if bases.contains_key(base) {
                deferred.push(class);
                continue;
            } else {
                return Err(error_at(
                    position,
                    format!(
                        "`class {class} : {base}` names a base without a `class` block: its \
                         base declares its object's functions, or is a class that defines them"
                    ),
                ));
            };
            let mut resolved = BTreeMap::new();
            for (function, _) in &objects[&root].functions {
                let definition = match (definitions.get(function), inherited) {
                    (Some(definition), _) => definition.clone(),
                    (None, Some(parent)) => through_base(&parent.definitions[function])
                        .ok_or_else(|| {
                            error_at(
                                position,
                                format!(
                                    "`class {class}` inherits `{base}`'s `function {function}`, \
                                     which reads its fields through `this->`; write its \
                                     definition: `function {function}(this) -> T {{ ... }}`"
                                ),
                            )
                        })?,
                    (None, None) => {
                        return Err(error_at(
                            position,
                            format!(
                                "`class {class}` defines `{root}`'s `function {function}` on \
                                 its own memory, where an inherited field is read through its \
                                 base: `function {function}(this) -> T {{ ... }}`"
                            ),
                        ));
                    }
                };
                resolved.insert(function.clone(), definition);
            }
            defining.insert(
                class.clone(),
                DefiningClass {
                    root,
                    base: base.clone(),
                    definitions: resolved,
                    position: position.clone(),
                    generic: generic_blocks.contains(class),
                },
            );
        }
        if deferred.len() == before {
            let (_, _, position) = &bases[deferred[0]];
            return Err(error_at(
                position,
                "`class` blocks name their bases in a cycle",
            ));
        }
        pending = deferred;
    }
    Ok((objects, defining))
}

/// A base's definition read on a derived class's memory: each `this->f`
/// read as `this->base.f`. `None` when it reads `this` otherwise.
fn through_base(definition: &[Spanned]) -> Option<Vec<Spanned>> {
    let mut tokens = Vec::with_capacity(definition.len() + 2);
    let mut index = 0;
    while index < definition.len() {
        if is_ident(definition.get(index), "this") {
            let Some((Token::Arrow, arrow)) = definition.get(index + 1) else {
                return None;
            };
            tokens.push(definition[index].clone());
            tokens.push((Token::Arrow, arrow.clone()));
            tokens.push((ident("base"), arrow.clone()));
            tokens.push((Token::Dot, arrow.clone()));
            index += 2;
            continue;
        }
        tokens.push(definition[index].clone());
        index += 1;
    }
    Some(tokens)
}

/// The function contracts at the top level, in order: a head whose
/// parameter list is followed, after an optional `const`, by a brace.
fn heads(source: &[Spanned]) -> Vec<Head> {
    let mut heads = Vec::new();
    let mut depth = 0i32;
    let mut item_start = 0;
    let mut index = 0;
    while index < source.len() {
        let token = &source[index].0;
        if depth == 0
            && *token == Token::LParen
            && let Some(head) = head_at(source, item_start, index)
        {
            index = head.end;
            item_start = head.end;
            heads.push(head);
            continue;
        }
        match token {
            Token::LBrace | Token::LParen | Token::LBracket => depth += 1,
            Token::RBrace | Token::RParen | Token::RBracket => {
                depth -= 1;
                if depth == 0 && *token == Token::RBrace {
                    item_start = index + 1;
                }
            }
            Token::Semicolon if depth == 0 => item_start = index + 1,
            _ => {}
        }
        index += 1;
    }
    heads
}

/// Whether a `class Name` block starts at `index`: `class`, not in a
/// template parameter list, `template<class T>`.
fn starts_class_block(source: &[Spanned], index: usize) -> bool {
    is_ident(source.get(index), "class")
        && !matches!(
            index.checked_sub(1).and_then(|at| source.get(at)),
            Some((Token::LessThan | Token::Comma, _))
        )
}

/// A `class` block starting at `index`, with a generic block's type
/// parameters, `template<class T> class Holder<T> { ... }`, and the index of
/// its `class`.
fn class_block_at(source: &[Spanned], index: usize) -> Option<(Option<Vec<String>>, usize)> {
    if let Some((parameters, after)) = template_prefix(source, index) {
        return is_ident(source.get(after), "class").then_some((Some(parameters), after));
    }
    starts_class_block(source, index).then_some((None, index))
}

fn head_at(source: &[Spanned], item_start: usize, list_open: usize) -> Option<Head> {
    let mut start = item_start;
    let mut template = Vec::new();
    if let Some((_, after)) = template_prefix(source, start) {
        template = source[start..after].to_vec();
        start = after;
    }
    if is_ident(source.get(start), "extern") || is_ident(source.get(start), "contract") {
        start += 1;
    }
    if [
        "abstract",
        "resource",
        "class",
        "template",
        "verifying",
        "theorem",
        "lemma",
        "predicate",
        "function",
    ]
    .iter()
    .any(|word| is_ident(source.get(start), word))
    {
        return None;
    }
    let Some((Token::Ident(method), _)) = list_open.checked_sub(1).and_then(|at| source.get(at))
    else {
        return None;
    };
    // The class is a name, or a template's instance, `Holder<int>::put`.
    let (class, name_start) = match list_open.checked_sub(2).map(|at| &source[at].0) {
        Some(Token::ColonColon) => {
            let colons = list_open - 2;
            let mut class_start = colons.checked_sub(1)?;
            if source[class_start].0 == Token::GreaterThan {
                let mut depth = 0usize;
                loop {
                    match source[class_start].0 {
                        Token::GreaterThan => depth += 1,
                        Token::LessThan => {
                            depth -= 1;
                            if depth == 0 {
                                break;
                            }
                        }
                        _ => {}
                    }
                    class_start = class_start.checked_sub(1)?;
                }
                class_start = class_start.checked_sub(1)?;
            }
            match class_at(source, class_start) {
                Some((class, end)) if end == colons => (Some(class), class_start),
                _ => (None, list_open - 1),
            }
        }
        _ => (None, list_open - 1),
    };
    if name_start <= start {
        return None;
    }
    let list_close = matching(source, list_open)?;
    let is_const = is_ident(source.get(list_close + 1), "const");
    let body_open = list_close + 1 + usize::from(is_const);
    if source.get(body_open).map(|(token, _)| token) != Some(&Token::LBrace) {
        return None;
    }
    let body_close = matching(source, body_open)?;
    let mut end = body_close + 1;
    if is_ident(source.get(end), "by")
        && source.get(end + 1).map(|(token, _)| token) == Some(&Token::LBrace)
        && let Some(proof_close) = matching(source, end + 1)
    {
        end = proof_close + 1;
    }
    Some(Head {
        start: item_start,
        template,
        result: source[start..name_start].to_vec(),
        class,
        method: method.clone(),
        list_open,
        list_close,
        is_const,
        body_open,
        body_close,
        end,
    })
}

/// One parameter of a head: its name and its type's tokens.
struct Parameter {
    name: String,
    tokens: Vec<Spanned>,
}

fn parameters(list: &[Spanned]) -> Vec<Parameter> {
    let mut parameters = Vec::new();
    let mut current: Vec<Spanned> = Vec::new();
    let mut depth = 0i32;
    let mut finish = |current: &mut Vec<Spanned>| {
        let tokens = std::mem::take(current);
        let name = match tokens.last() {
            Some((Token::Ident(name), _)) => name.clone(),
            _ => return,
        };
        parameters.push(Parameter { name, tokens });
    };
    for spanned in list {
        match spanned.0 {
            Token::LParen | Token::LBracket | Token::LessThan => depth += 1,
            Token::RParen | Token::RBracket | Token::GreaterThan => depth -= 1,
            Token::Comma if depth == 0 => {
                finish(&mut current);
                continue;
            }
            _ => {}
        }
        current.push(spanned.clone());
    }
    finish(&mut current);
    parameters
}

/// The class a parameter `const Shape& x` or `Holder<int>& x` refers to,
/// and whether the reference is `const`.
fn referenced_class(parameter: &Parameter) -> Option<(bool, String)> {
    let tokens = &parameter.tokens;
    let constant = is_ident(tokens.first(), "const");
    let (class, end) = class_at(tokens, usize::from(constant))?;
    (tokens.get(end).map(|(token, _)| token) == Some(&Token::Amp) && end + 2 == tokens.len())
        .then_some((constant, class))
}

/// The object class a parameter `const Shape& x` or `Shape& x` refers to,
/// and whether the reference is `const`, which keeps the object's state.
fn object_parameter<'a>(
    parameter: &Parameter,
    objects: &'a BTreeMap<String, ObjectClass>,
    references: &BTreeMap<String, String>,
) -> Option<(&'a ObjectClass, bool)> {
    let (constant, class) = referenced_class(parameter)?;
    let root = references.get(&class)?;
    objects.get(root).map(|object| (object, constant))
}

/// The handle owned for a holder's object: `__object_this:
/// Shape__object(this)` or `__object_x: Shape__object(&x)`, and, when
/// `kept`, that it keeps its fields.
fn object_clauses(
    holder: &str,
    object: &ObjectClass,
    kept: bool,
    position: &SourcePosition,
) -> (Vec<Spanned>, Vec<Spanned>) {
    let mut owns = at(
        position,
        vec![ident("owns"), ident(&handle(holder)), Token::Colon],
    );
    owns.extend(family_use(object, position));
    owns.push((Token::LParen, position.clone()));
    if holder != "this" {
        owns.push((Token::Amp, position.clone()));
    }
    owns.extend(at(
        position,
        vec![ident(holder), Token::RParen, Token::Semicolon],
    ));
    let mut keeps = Vec::new();
    for (function, _) in object.functions.iter().filter(|_| kept) {
        keeps.extend(at(position, vec![ident("ensures")]));
        keeps.extend(field_read(holder, function, position));
        keeps.extend(at(
            position,
            vec![Token::EqualEqual, ident("old"), Token::LParen],
        ));
        keeps.extend(field_read(holder, function, position));
        keeps.extend(at(position, vec![Token::RParen, Token::Semicolon]));
    }
    (owns, keeps)
}

/// `abstract resource Family(object: int32*) { field f: T; ... }`, or a
/// generic block's `abstract resource Family<T>(...)`; nothing for an
/// instance of a generic block.
fn object_declaration(object: &ObjectClass, position: &SourcePosition) -> Vec<Spanned> {
    let Some(parameters) = &object.declares else {
        return Vec::new();
    };
    let mut tokens = at(
        position,
        vec![ident("abstract"), ident("resource"), ident(&object.family)],
    );
    if !parameters.is_empty() {
        tokens.push((Token::LessThan, position.clone()));
        for (index, parameter) in parameters.iter().enumerate() {
            if index > 0 {
                tokens.push((Token::Comma, position.clone()));
            }
            tokens.push((ident(parameter), position.clone()));
        }
        tokens.push((Token::GreaterThan, position.clone()));
    }
    tokens.extend(at(
        position,
        vec![
            Token::LParen,
            ident("object"),
            Token::Colon,
            ident("int32"),
            Token::Star,
            Token::RParen,
            Token::LBrace,
        ],
    ));
    for (function, result) in &object.functions {
        tokens.extend(at(
            position,
            vec![ident("field"), ident(function), Token::Colon],
        ));
        tokens.extend(result.iter().cloned());
        tokens.extend(at(position, vec![Token::Semicolon]));
    }
    tokens.extend(at(position, vec![Token::RBrace]));
    tokens
}

/// `size(this)` read as `(definition)`.
fn on_memory(
    clause: &[Spanned],
    definer: &DefiningClass,
    functions: &[(String, Vec<Spanned>)],
    kept: bool,
) -> Vec<Spanned> {
    rewrite_calls(clause, "this", functions, kept, &|function, position| {
        let mut tokens = vec![(Token::LParen, position.clone())];
        tokens.extend(definer.definitions[function].iter().cloned());
        tokens.push((Token::RParen, position.clone()));
        tokens
    })
}

/// A function contract whose receiver or parameters hold objects, or a
/// method of a defining class, which is stated on its own memory.
fn rewrite_function(
    source: &[Spanned],
    head: &Head,
    objects: &BTreeMap<String, ObjectClass>,
    defining: &BTreeMap<String, DefiningClass>,
    references: &BTreeMap<String, String>,
    records: &BTreeMap<String, String>,
    output: &mut Vec<Spanned>,
) -> Result<(), ClickError> {
    let own = parameters(&source[head.list_open + 1..head.list_close]);
    let receiver_object = head.class.as_ref().and_then(|class| objects.get(class));
    let definer = head.class.as_ref().and_then(|class| defining.get(class));
    // Each holder of an object, and whether it keeps the object's state: a
    // `const` receiver or reference does, and a mutable one may change it.
    let mut holders = Vec::new();
    if let Some(object) = receiver_object {
        holders.push(("this".to_string(), object, head.is_const));
    }
    for parameter in &own {
        if let Some((object, kept)) = object_parameter(parameter, objects, references) {
            holders.push((parameter.name.clone(), object, kept));
        }
    }
    if holders.is_empty() && definer.is_none() {
        output.extend(source[head.start..head.end].iter().cloned());
        return Ok(());
    }
    let position = source[head.body_open].1.clone();
    let read_objects = |clause: Vec<Spanned>| {
        holders
            .iter()
            .fold(clause, |clause, (holder, object, kept)| {
                rewrite_calls(
                    &clause,
                    holder,
                    &object.functions,
                    *kept,
                    &|function, position| field_read(holder, function, position),
                )
            })
    };
    let mut clauses = Vec::new();
    let mut keeps = Vec::new();
    for (holder, object, kept) in &holders {
        let (owns, keep) = object_clauses(holder, object, *kept, &position);
        clauses.push(owns[..owns.len() - 1].to_vec());
        keeps.extend(split_clauses(&keep));
    }
    let mut interface_contract = None;
    if let Some(definer) = definer {
        let class = head.class.as_deref().unwrap_or_default();
        let root = &objects[&definer.root];
        let functions = root
            .functions
            .iter()
            .map(|(function, _)| (function.clone(), definer.definitions[function].clone()))
            .collect::<Vec<_>>();
        // A `const` method only views its memory, so a caller keeps every
        // field across the call, not only the functions' definitions.
        let memory = at(
            &position,
            vec![
                ident(if head.is_const { "views" } else { "owns" }),
                Token::Star,
                ident("this"),
            ],
        );
        let own_clauses = split_clauses(&source[head.body_open + 1..head.body_close])
            .iter()
            .map(|clause| read_objects(on_memory(clause, definer, &functions, head.is_const)))
            .collect::<Vec<_>>();
        let writes_requires = own_clauses
            .iter()
            .any(|clause| is_ident(clause.first(), "requires"));
        // The object class's interface for this method, read on this
        // class's memory, then that a `const` method keeps the functions.
        let interface = root.methods.get(&head.method);
        let renames = interface
            .filter(|interface| interface.parameters.len() == own.len())
            .map(|interface| {
                interface
                    .parameters
                    .iter()
                    .zip(&own)
                    .filter(|(from, to)| *from != &to.name)
                    .map(|(from, to)| (from.clone(), to.name.clone()))
                    .collect::<BTreeMap<_, _>>()
            })
            .unwrap_or_default();
        let mut interface_clauses = Vec::new();
        let mut ensures = 0usize;
        for clause in interface.map_or(&[][..], |interface| &interface.clauses) {
            let clause = read_objects(on_memory(
                &rename(clause, &renames),
                definer,
                &functions,
                head.is_const,
            ));
            if is_ident(clause.first(), "ensures") {
                let named = matches!(clause.get(1), Some((Token::Ident(_), _)))
                    && clause.get(2).map(|(token, _)| token) == Some(&Token::Colon);
                let mut labeled = vec![clause[0].clone()];
                if named {
                    let Some((Token::Ident(name), label_position)) = clause.get(1) else {
                        unreachable!()
                    };
                    labeled.push((ident(&format!("interface_{name}")), label_position.clone()));
                    labeled.extend(clause[2..].iter().cloned());
                } else {
                    labeled.push((
                        ident(&format!("interface_ensures_{ensures}")),
                        clause[0].1.clone(),
                    ));
                    labeled.push((Token::Colon, clause[0].1.clone()));
                    labeled.extend(clause[1..].iter().cloned());
                }
                ensures += 1;
                interface_clauses.push((clause, labeled));
            } else {
                interface_clauses.push((clause.clone(), clause));
            }
        }
        if head.is_const {
            for (function, definition) in &functions {
                let mut clause = at(
                    &position,
                    vec![
                        ident("ensures"),
                        ident(&format!("interface_keeps_{function}")),
                        Token::Colon,
                        Token::LParen,
                    ],
                );
                clause.extend(definition.iter().cloned());
                clause.extend(at(
                    &position,
                    vec![
                        Token::RParen,
                        Token::EqualEqual,
                        ident("old"),
                        Token::LParen,
                        Token::LParen,
                    ],
                ));
                clause.extend(definition.iter().cloned());
                clause.extend(at(&position, vec![Token::RParen, Token::RParen]));
                interface_clauses.push((clause.clone(), clause));
            }
        }
        clauses.insert(0, memory.clone());
        clauses.extend(own_clauses.iter().cloned());
        for (plain, labeled) in &interface_clauses {
            let requires = is_ident(plain.first(), "requires");
            if (requires && writes_requires)
                || own_clauses.iter().any(|clause| same_tokens(clause, plain))
            {
                continue;
            }
            clauses.push(labeled.clone());
        }
        // The interface as a `contract` of this method's parameters, with a
        // receiver of this class.
        if interface.is_some() {
            // A generic method's interface is stated once for every type, as
            // the method is verified.
            let mut contract = head.template.clone();
            contract.push((ident("contract"), position.clone()));
            contract.extend(head.result.iter().cloned());
            contract.extend(at(
                &position,
                vec![
                    ident(&implementation_interface_contract(&method_name(
                        class,
                        &head.method,
                    ))),
                    Token::LParen,
                ],
            ));
            if head.is_const {
                contract.push((ident("const"), position.clone()));
            }
            contract.extend(at(
                &position,
                vec![
                    ident("struct"),
                    ident(&record_of(class, records)),
                    Token::Star,
                    ident("this"),
                ],
            ));
            for parameter in &own {
                contract.push((Token::Comma, position.clone()));
                contract.extend(parameter.tokens.iter().cloned());
            }
            contract.extend(at(&position, vec![Token::RParen, Token::LBrace]));
            contract.extend(memory.iter().cloned());
            contract.push((Token::Semicolon, position.clone()));
            for (plain, _) in &interface_clauses {
                contract.extend(plain.iter().cloned());
                contract.push((Token::Semicolon, position.clone()));
            }
            contract.push((Token::RBrace, position.clone()));
            interface_contract = Some(contract);
        }
    } else {
        clauses.extend(
            split_clauses(&source[head.body_open + 1..head.body_close])
                .into_iter()
                .map(read_objects),
        );
    }
    clauses.extend(keeps);
    output.extend(source[head.start..=head.body_open].iter().cloned());
    for clause in clauses {
        let end = clause
            .last()
            .map(|(_, position)| position.clone())
            .unwrap_or_else(|| position.clone());
        output.extend(clause);
        output.push((Token::Semicolon, end));
    }
    output.extend(source[head.body_close..head.end].iter().cloned());
    if let Some(contract) = interface_contract {
        output.extend(contract);
    }
    Ok(())
}

/// The contracts of the dispatches the importer names for calls through a
/// reference to `class`, which another class derives from: each method of
/// `class` that overrides one of the object class's is called as that
/// method's interface, holding the object, whichever override runs.
fn dispatch_contracts(
    source: &[Spanned],
    found: &[Head],
    class: &str,
    definer: &DefiningClass,
    objects: &BTreeMap<String, ObjectClass>,
    defining: &BTreeMap<String, DefiningClass>,
    references: &BTreeMap<String, String>,
    records: &BTreeMap<String, String>,
) -> Result<Vec<Spanned>, ClickError> {
    let root = &objects[&definer.root];
    let mut output = Vec::new();
    for head in found {
        if head.class.as_deref() != Some(class) {
            continue;
        }
        let Some(interface) = root.methods.get(&head.method) else {
            continue;
        };
        let own = parameters(&source[head.list_open + 1..head.list_close]);
        if interface.parameters.len() != own.len() {
            continue;
        }
        let renames = interface
            .parameters
            .iter()
            .zip(&own)
            .filter(|(from, to)| *from != &to.name)
            .map(|(from, to)| (from.clone(), to.name.clone()))
            .collect::<BTreeMap<_, _>>();
        let position = source[head.body_open].1.clone();
        // The interface, written as a method of the object class with this
        // method's parameters, rewritten as such a method is.
        let mut method = at(&position, vec![ident("extern")]);
        method.extend(head.result.iter().cloned());
        let name_start = method.len();
        method.extend(at(
            &position,
            vec![ident(&definer.root), Token::ColonColon, ident(&head.method)],
        ));
        method.extend(source[head.list_open..=head.list_close].iter().cloned());
        if head.is_const {
            method.push((ident("const"), position.clone()));
        }
        method.push((Token::LBrace, position.clone()));
        for clause in &interface.clauses {
            method.extend(rename(clause, &renames));
            method.push((Token::Semicolon, position.clone()));
        }
        method.push((Token::RBrace, position.clone()));
        let interface_head = head_at(&method, 0, name_start + 3)
            .expect("a dispatch's interface is a function contract");
        let mut rewritten = Vec::new();
        rewrite_function(
            &method,
            &interface_head,
            objects,
            defining,
            references,
            records,
            &mut rewritten,
        )?;
        // Its head names the dispatch and its receiver.
        let mut dispatch = at(&position, vec![ident("extern")]);
        dispatch.extend(head.result.iter().cloned());
        dispatch.extend(at(
            &position,
            vec![
                ident(&crate::languages::cpp::names::object_dispatch_name(
                    class,
                    &head.method,
                )),
                Token::LParen,
            ],
        ));
        if head.is_const {
            dispatch.push((ident("const"), position.clone()));
        }
        dispatch.extend(at(
            &position,
            vec![
                ident("struct"),
                ident(&record_of(class, records)),
                Token::Star,
                ident("this"),
            ],
        ));
        for parameter in &own {
            dispatch.push((Token::Comma, position.clone()));
            dispatch.extend(parameter.tokens.iter().cloned());
        }
        dispatch.extend(at(&position, vec![Token::RParen, Token::LBrace]));
        let body = interface_head.body_open - interface_head.start + 1;
        dispatch.extend(rewritten.into_iter().skip(body));
        output.extend(dispatch);
    }
    Ok(output)
}

/// The trusted contracts of the functions the importer places where a
/// reference to `class` becomes a reference to its object class, and back:
/// the pack consumes the class's memory and produces the object, whose
/// fields are the class's definitions on that memory; the unpack returns
/// the memory, whose definitions are the object's fields. A `const`
/// reference's pair leaves the memory with the caller, viewed.
fn coercion_contracts(
    class: &str,
    target: &str,
    definer: &DefiningClass,
    object: &ObjectClass,
    records: &BTreeMap<String, String>,
    position: &SourcePosition,
) -> Vec<Spanned> {
    // The importer names the functions by the records' layout names,
    // `Wrap__int` for `Wrap<int>`.
    let target = record_of(target, records);
    let target = target.as_str();
    let class = record_of(class, records);
    let class = class.as_str();
    let receiver = BTreeMap::from([("this".to_string(), "object".to_string())]);
    let holder = handle("object");
    let head = |name: &str| {
        at(
            position,
            vec![
                ident("extern"),
                ident("void"),
                ident(name),
                Token::LParen,
                ident("const"),
                ident("struct"),
                ident(class),
                Token::Star,
                ident("object"),
                Token::RParen,
                Token::LBrace,
            ],
        )
    };
    let instance = |verb: &str| {
        let mut tokens = at(position, vec![ident(verb), ident(&holder), Token::Colon]);
        tokens.extend(family_use(object, position));
        tokens.extend(at(
            position,
            vec![
                Token::LParen,
                ident("object"),
                Token::RParen,
                Token::Semicolon,
            ],
        ));
        tokens
    };
    let memory = |verb: &str| {
        at(
            position,
            vec![ident(verb), Token::Star, ident("object"), Token::Semicolon],
        )
    };
    let root = target;
    let mut tokens = head(&crate::languages::cpp::names::object_pack_name(class, root));
    tokens.extend(memory("consumes"));
    tokens.extend(instance("produces"));
    for (function, _) in &object.functions {
        tokens.push((ident("ensures"), position.clone()));
        tokens.extend(field_read("object", function, position));
        tokens.extend(at(
            position,
            vec![
                Token::EqualEqual,
                ident("old"),
                Token::LParen,
                Token::LParen,
            ],
        ));
        tokens.extend(rename(&definer.definitions[function], &receiver));
        tokens.extend(at(
            position,
            vec![Token::RParen, Token::RParen, Token::Semicolon],
        ));
    }
    tokens.push((Token::RBrace, position.clone()));
    tokens.extend(head(&crate::languages::cpp::names::object_unpack_name(
        class, root,
    )));
    tokens.extend(instance("consumes"));
    tokens.extend(memory("produces"));
    for (function, _) in &object.functions {
        tokens.extend(at(position, vec![ident("ensures"), Token::LParen]));
        tokens.extend(rename(&definer.definitions[function], &receiver));
        tokens.extend(at(
            position,
            vec![
                Token::RParen,
                Token::EqualEqual,
                ident("old"),
                Token::LParen,
            ],
        ));
        tokens.extend(field_read("object", function, position));
        tokens.extend(at(position, vec![Token::RParen, Token::Semicolon]));
    }
    tokens.push((Token::RBrace, position.clone()));
    // Where the reference is `const`, the memory stays the caller's, lent
    // to a resource the pack produces beside the object: while the callee
    // holds the object, nothing changes the memory or hands it over again,
    // so the caller keeps every field. The unpack gives both up.
    let lend = crate::languages::cpp::names::object_lend_name(class, root);
    let lent = |verb: &str| {
        at(
            position,
            vec![
                ident(verb),
                ident(&lend),
                Token::LParen,
                ident("object"),
                Token::RParen,
                Token::Semicolon,
            ],
        )
    };
    tokens.extend(at(
        position,
        vec![
            ident("resource"),
            ident(&lend),
            Token::LParen,
            ident("object"),
            Token::Colon,
            ident("struct"),
            ident(class),
            Token::Star,
            Token::RParen,
            Token::LBrace,
            ident("views"),
            Token::Star,
            ident("object"),
            Token::Semicolon,
            Token::RBrace,
        ],
    ));
    tokens.extend(head(&crate::languages::cpp::names::object_const_pack_name(
        class, root,
    )));
    tokens.extend(memory("views"));
    tokens.extend(lent("produces"));
    tokens.extend(instance("produces"));
    for (function, _) in &object.functions {
        tokens.push((ident("ensures"), position.clone()));
        tokens.extend(field_read("object", function, position));
        tokens.extend(at(position, vec![Token::EqualEqual, Token::LParen]));
        tokens.extend(rename(&definer.definitions[function], &receiver));
        tokens.extend(at(position, vec![Token::RParen, Token::Semicolon]));
    }
    tokens.push((Token::RBrace, position.clone()));
    tokens.extend(head(
        &crate::languages::cpp::names::object_const_unpack_name(class, root),
    ));
    tokens.extend(lent("consumes"));
    tokens.extend(instance("consumes"));
    tokens.push((Token::RBrace, position.clone()));
    tokens
}
