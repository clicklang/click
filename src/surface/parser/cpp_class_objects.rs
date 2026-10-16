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
    functions: Vec<(String, Vec<Spanned>)>,
    methods: BTreeMap<String, Interface>,
}

/// An object class method's interface, as its sidecar contract writes it.
struct Interface {
    parameters: Vec<String>,
    clauses: Vec<Vec<Spanned>>,
}

/// A class that defines an object class's functions on its own memory.
struct DefiningClass {
    root: String,
    definitions: BTreeMap<String, Vec<Spanned>>,
}

/// A function contract at the top level of the sidecar.
struct Head {
    /// The item's first token, after an `extern` or `contract` keyword.
    start: usize,
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

/// The name of the abstract resource that is class `class`'s object.
pub(crate) fn object_family(class: &str) -> String {
    format!("{class}__object")
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
}

/// Rewrites the class object state of a C++ sidecar, and returns the
/// methods it states on objects.
pub(super) fn rewrite_class_objects(
    tokens: Vec<Token>,
    positions: Vec<SourcePosition>,
) -> Result<(Vec<Token>, Vec<SourcePosition>, ObjectMethods), ClickError> {
    let source: Vec<Spanned> = tokens.into_iter().zip(positions).collect();
    let (mut objects, defining) = classes(&source)?;
    if objects.is_empty() {
        let (tokens, positions) = source.into_iter().unzip();
        return Ok((tokens, positions, ObjectMethods::default()));
    }
    let found = heads(&source);
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
    let mut output = Vec::with_capacity(source.len());
    let on_memory = found
        .iter()
        .filter_map(|head| {
            let class = head.class.as_ref()?;
            defining
                .contains_key(class)
                .then(|| method_name(class, &head.method))
        })
        .collect();
    let mut pending = found.into_iter().peekable();
    let mut index = 0;
    let mut depth = 0i32;
    while index < source.len() {
        if let Some(head) = pending.next_if(|head| head.start == index) {
            rewrite_function(&source, &head, &objects, &defining, &mut output)?;
            index = head.end;
            continue;
        }
        if depth == 0
            && is_ident(source.get(index), "class")
            && let Some((Token::Ident(class), position)) = source.get(index + 1)
            && let Some(open) = (index + 2..source.len()).find(|&at| source[at].0 == Token::LBrace)
            && let Some(close) = matching(&source, open)
        {
            if let Some(object) = objects.get(class) {
                output.extend(object_declaration(object, position));
            } else if let Some(definer) = defining.get(class) {
                output.extend(coercion_contracts(
                    class,
                    definer,
                    &objects[&definer.root],
                    position,
                ));
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
        },
    ))
}

/// The `class` blocks: those that declare their object's functions, and
/// those that define them after naming a base.
fn classes(
    source: &[Spanned],
) -> Result<
    (
        BTreeMap<String, ObjectClass>,
        BTreeMap<String, DefiningClass>,
    ),
    ClickError,
> {
    let mut objects = BTreeMap::new();
    // Each defining class's base and own definitions, before its root is known.
    let mut bases = BTreeMap::new();
    let mut depth = 0i32;
    let mut index = 0;
    while index < source.len() {
        if depth == 0
            && is_ident(source.get(index), "class")
            && let Some((Token::Ident(class), position)) = source.get(index + 1)
        {
            let (base, open) = match source.get(index + 2).map(|(token, _)| token) {
                Some(Token::Colon) => match source.get(index + 3) {
                    Some((Token::Ident(base), _)) => (Some(base.clone()), index + 4),
                    _ => (None, index + 3),
                },
                _ => (None, index + 2),
            };
            if source.get(open).map(|(token, _)| token) != Some(&Token::LBrace) {
                return Err(error_at(
                    position,
                    "a `class` block is written `class Name { ... }` or `class Name : Base { ... }`",
                ));
            }
            let close = matching(source, open)
                .ok_or_else(|| error_at(position, "unterminated `class` block"))?;
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
            match (base, declared.is_empty(), defined.is_empty()) {
                (None, false, true) => {
                    objects.insert(
                        class.clone(),
                        ObjectClass {
                            family: object_family(class),
                            functions: declared,
                            methods: BTreeMap::new(),
                        },
                    );
                }
                (Some(base), true, _) => {
                    bases.insert(class.clone(), (base, defined, position.clone()));
                }
                _ => {
                    return Err(error_at(
                        position,
                        "a `class` block either declares its object's functions, \
                         `class Shape { function size(this) -> int32; }`, or names its base and \
                         defines them, `class Square : Shape { function size(this) -> int32 { \
                         this->side } }`",
                    ));
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
        index += 1;
    }
    // Each class defines the functions on its own memory. Its base is the
    // class whose object it is: a class deriving from a defining class would
    // run that class's methods on an object its own definitions describe.
    let mut defining = BTreeMap::new();
    for (class, (base, definitions, position)) in &bases {
        if !objects.contains_key(base) {
            return Err(error_at(
                position,
                format!(
                    "`class {class} : {base}` names a base whose `class` block does not declare \
                     its object's functions; only a direct subclass of that class defines them"
                ),
            ));
        }
        let root = base.clone();
        for (function, _) in &objects[&root].functions {
            if !definitions.contains_key(function) {
                return Err(error_at(
                    position,
                    format!(
                        "`class {class}` defines `{root}`'s `function {function}` on its own \
                         memory, where an inherited field is read through its base: \
                         `function {function}(this) -> T {{ ... }}`"
                    ),
                ));
            }
        }
        defining.insert(
            class.clone(),
            DefiningClass {
                root,
                definitions: definitions.clone(),
            },
        );
    }
    Ok((objects, defining))
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

fn head_at(source: &[Spanned], item_start: usize, list_open: usize) -> Option<Head> {
    let mut start = item_start;
    if is_ident(source.get(start), "extern") || is_ident(source.get(start), "contract") {
        start += 1;
    }
    if [
        "abstract",
        "resource",
        "class",
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
    let (class, name_start) = match (
        list_open.checked_sub(2).map(|at| &source[at].0),
        list_open.checked_sub(3).and_then(|at| source.get(at)),
    ) {
        (Some(Token::ColonColon), Some((Token::Ident(class), _))) => {
            (Some(class.clone()), list_open - 3)
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

/// The object class a parameter `const Shape& x` or `Shape& x` refers to,
/// and whether the reference is `const`, which keeps the object's state.
fn object_parameter<'a>(
    parameter: &Parameter,
    objects: &'a BTreeMap<String, ObjectClass>,
) -> Option<(&'a ObjectClass, bool)> {
    let (constant, class) = match parameter.tokens.as_slice() {
        [
            (Token::Ident(word), _),
            (Token::Ident(class), _),
            (Token::Amp, _),
            _,
        ] if word == "const" => (true, class),
        [(Token::Ident(class), _), (Token::Amp, _), _] => (false, class),
        _ => return None,
    };
    objects.get(class).map(|object| (object, constant))
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
        vec![
            ident("owns"),
            ident(&handle(holder)),
            Token::Colon,
            ident(&object.family),
            Token::LParen,
        ],
    );
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

/// `abstract resource Family(object: int32*) { field f: T; ... }`.
fn object_declaration(object: &ObjectClass, position: &SourcePosition) -> Vec<Spanned> {
    let mut tokens = at(
        position,
        vec![
            ident("abstract"),
            ident("resource"),
            ident(&object.family),
            Token::LParen,
            ident("object"),
            Token::Colon,
            ident("int32"),
            Token::Star,
            Token::RParen,
            Token::LBrace,
        ],
    );
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
        if let Some((object, kept)) = object_parameter(parameter, objects) {
            holders.push((parameter.name.clone(), object, kept));
        }
    }
    if holders.is_empty() && definer.is_none() {
        output.extend(source[head.start..head.end].iter().cloned());
        return Ok(());
    }
    let position = source[head.body_open].1.clone();
    let read_objects = |clause: Vec<Spanned>| {
        holders.iter().fold(clause, |clause, (holder, object, kept)| {
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
        let memory = at(&position, vec![ident("owns"), Token::Star, ident("this")]);
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
            let mut contract = at(&position, vec![ident("contract")]);
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
                vec![ident("struct"), ident(class), Token::Star, ident("this")],
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

/// The trusted contracts of the functions the importer places where a
/// reference to `class` becomes a reference to its object class, and back:
/// the pack consumes the class's memory and produces the object, whose
/// fields are the class's definitions on that memory; the unpack returns
/// the memory, whose definitions are the object's fields.
fn coercion_contracts(
    class: &str,
    definer: &DefiningClass,
    object: &ObjectClass,
    position: &SourcePosition,
) -> Vec<Spanned> {
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
        at(
            position,
            vec![
                ident(verb),
                ident(&holder),
                Token::Colon,
                ident(&object.family),
                Token::LParen,
                ident("object"),
                Token::RParen,
                Token::Semicolon,
            ],
        )
    };
    let memory = |verb: &str| {
        at(
            position,
            vec![ident(verb), Token::Star, ident("object"), Token::Semicolon],
        )
    };
    let root = &definer.root;
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
    tokens
}
