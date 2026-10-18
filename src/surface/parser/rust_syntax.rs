//! The Rust spelling of a sidecar: `fn` signatures, `impl` blocks, slices,
//! references, lifetimes and `as` casts, admitted when a `verifying` source
//! is Rust.

use super::*;

/// The importer name of the crate trait at `path` with type `arguments`:
/// `traits::Shape`, or `traits::Scale<i32>`.
fn trait_instance_name(path: &[String], arguments: &[String]) -> String {
    let mut name = crate::languages::rust::names::path_name(
        &path.iter().map(String::as_str).collect::<Vec<_>>(),
    );
    for argument in arguments {
        crate::languages::rust::names::push_type_argument(&mut name, argument);
    }
    name
}

impl Parser {
    /// A Rust sidecar states its signature as Rust does:
    /// `fn name(a: T, b: U) -> R`, with references, slices, and methods in
    /// `impl` blocks. C-shaped function contracts are refused for Rust sources.
    #[inline(never)]
    pub(super) fn parse_rust_function_signature(
        &mut self,
    ) -> Result<ParsedFunctionSignature, ClickError> {
        // A generic function's own abstract type parameters are in scope for
        // its signature only.
        let previous_abstract = self.rust_abstract_type_parameters.clone();
        let signature = self.parse_rust_function_signature_in_scope();
        self.rust_abstract_type_parameters = previous_abstract;
        signature
    }

    fn parse_rust_function_signature_in_scope(
        &mut self,
    ) -> Result<ParsedFunctionSignature, ClickError> {
        if !self.verifies_rust() {
            return Err(self.error(
                "a `fn` signature is the Rust spelling; a C or C++ source's contract is written `type name(type parameter, ...)`",
            ));
        }
        self.expect_ident_spelling("fn")?;
        let path = self.expect_rust_path("function name")?;
        self.rust_trait_type_parameters.clear();
        let callable_parameters = self.parse_rust_generic_parameters()?;
        let name = if self.rust_impl_type.is_some() || self.rust_trait_interface.is_some() {
            // A method's own name; an item inside it, `compute::LIMIT`,
            // follows as the importer writes path segments.
            crate::languages::rust::names::method_path_name(
                &path.iter().map(String::as_str).collect::<Vec<_>>(),
            )
        } else {
            crate::languages::rust::names::path_name(
                &path.iter().map(String::as_str).collect::<Vec<_>>(),
            )
        };
        self.expect(Token::LParen)?;
        let mut parameters = Vec::new();
        let mut struct_params = BTreeMap::new();
        // The importer encodes a method's receiver type and declaration path
        // in its identity. Its receiver is the first parameter, named `self`.
        let name = match self.rust_impl_type.clone() {
            // A trait interface does not know the receiver's concrete fields.
            // Declared object state is handled by `rewrite_trait_objects`.
            None if let Some(interface) = self.rust_trait_interface.clone() => {
                let Some(mut receiver) = self.parse_rust_receiver("")? else {
                    return Err(
                        self.error("a trait method's interface takes `&self` or `&mut self`")
                    );
                };
                if !receiver.struct_pointer {
                    return Err(
                        self.error("a trait method's interface takes `&self` or `&mut self`")
                    );
                }
                receiver.struct_name = None;
                receiver.struct_pointer = false;
                parameters.push(
                    self.parse_parameter_array_suffix("self".into(), receiver)?
                        .parameter,
                );
                if self.peek() == Some(&Token::Comma) {
                    self.position += 1;
                }
                let mut encoded = interface;
                crate::languages::rust::names::push_path_segment(&mut encoded, &name);
                encoded
            }
            Some(impl_type) => {
                if let Some(receiver) = self.parse_rust_receiver(&impl_type)? {
                    let parsed = self.parse_parameter_array_suffix("self".into(), receiver)?;
                    if let Some(struct_name) = parsed.struct_name {
                        struct_params.insert(parsed.parameter.name.clone(), struct_name);
                    }
                    parameters.push(parsed.parameter);
                    if self.peek() == Some(&Token::Comma) {
                        self.position += 1;
                    }
                }
                match (&self.rust_impl_trait, &self.rust_impl_method_suffix) {
                    (Some(trait_name), _) => crate::languages::rust::names::trait_method_name(
                        &impl_type, trait_name, &name,
                    ),
                    (None, Some(suffix)) => format!("{impl_type}_{name}_{suffix}"),
                    (None, None) => self.rust_inherent_method(&impl_type, &name)?,
                }
            }
            None => name,
        };
        let mut rust_slice_parameters = Vec::new();
        while self.peek() != Some(&Token::RParen) {
            let parameter_name = self.expect_ident("parameter name")?;
            self.expect(Token::Colon)?;
            if let Some(element) = self.parse_rust_slice_type()? {
                // `bytes: &[T]` is the pointer and length Rust passes. The
                // sidecar names the slice once and reads `bytes.len()`.
                let length = format!("{parameter_name}_len");
                self.rust_slice_params.insert(parameter_name.clone());
                rust_slice_parameters.push(parameter_name.clone());
                parameters.push(
                    self.parse_parameter_array_suffix(parameter_name, element)?
                        .parameter,
                );
                let length_type = ParsedType {
                    c_type: C0Type::UInt64(LongRank::Long),
                    struct_name: None,
                    struct_pointer: false,
                    constant: false,
                    pointee_constant: false,
                    reference: false,
                };
                parameters.push(
                    self.parse_parameter_array_suffix(length, length_type)?
                        .parameter,
                );
                if self.peek() != Some(&Token::Comma) {
                    break;
                }
                self.position += 1;
                continue;
            }
            let dyn_fn = self.peek() == Some(&Token::Amp)
                && matches!(self.tokens.get(self.position + 1), Some(Token::Ident(word)) if word == "dyn")
                && matches!(self.tokens.get(self.position + 2), Some(Token::Ident(word)) if word == "Fn");
            // `f: F` of a `<F: Fn(i32) -> i32>` parameter.
            if let Some(word) = self.peek_ident()
                && let Some((c_type, signature)) = callable_parameters.get(word).cloned()
                && matches!(self.peek_next(), Some(Token::Comma | Token::RParen))
            {
                self.position += 1;
                parameters.push(FunctionParameter {
                    click_type: ClickType::C(c_type),
                    name: parameter_name,
                    struct_name: None,
                    function_pointer_signature: Some(signature),
                    constant: false,
                    pointee_constant: false,
                    reference: false,
                });
                if self.peek() != Some(&Token::Comma) {
                    break;
                }
                self.position += 1;
                continue;
            }
            let impl_fn = self.peek_ident() == Some("impl");
            if dyn_fn
                || impl_fn
                || (self.peek_ident() == Some("fn") && self.peek_next() == Some(&Token::LParen))
            {
                let (c_type, signature) = if dyn_fn {
                    self.parse_rust_dyn_fn_type()?
                } else if impl_fn {
                    self.parse_rust_impl_fn_type()?
                } else {
                    self.parse_rust_fn_pointer_type()?
                };
                parameters.push(FunctionParameter {
                    click_type: ClickType::C(c_type),
                    name: parameter_name,
                    struct_name: None,
                    function_pointer_signature: Some(signature),
                    constant: false,
                    pointee_constant: false,
                    reference: false,
                });
                if self.peek() != Some(&Token::Comma) {
                    break;
                }
                self.position += 1;
                continue;
            }
            let parsed_type = self.parse_rust_type()?;
            let parsed = self.parse_parameter_array_suffix(parameter_name, parsed_type)?;
            if let Some(struct_name) = parsed.struct_name {
                struct_params.insert(parsed.parameter.name.clone(), struct_name);
            }
            parameters.push(parsed.parameter);
            if self.peek() != Some(&Token::Comma) {
                break;
            }
            self.position += 1;
        }
        self.expect(Token::RParen)?;
        let parsed_return_type = if self.peek() == Some(&Token::Arrow) {
            self.position += 1;
            self.parse_rust_type()?
        } else {
            ParsedType {
                c_type: C0Type::Void,
                struct_name: None,
                struct_pointer: false,
                constant: false,
                pointee_constant: false,
                reference: false,
            }
        };
        let return_type = match parsed_return_type.struct_name.as_deref() {
            Some(struct_name) => self.scalar_struct_value_type(struct_name)?,
            None => parsed_return_type.c_type,
        };
        let diverges = if self.peek_ident() == Some("diverges") {
            self.position += 1;
            true
        } else {
            false
        };
        Ok(ParsedFunctionSignature {
            signature: FunctionSignature {
                c_source: None,
                return_type,
                return_pointee_constant: false,
                return_reference: false,
                name,
                parameters,
                exceptional_type: None,
                diverges,
                declared_loadable_bytes: Vec::new(),
                rust_spelling: super::RustSignatureSpelling::rust(rust_slice_parameters),
            },
            struct_params,
            struct_array_params: BTreeSet::new(),
            reference_params: BTreeSet::new(),
            return_struct_name: parsed_return_type.struct_name,
        })
    }

    /// `impl Type { ... }` or `impl Trait for Type { ... }`: each `fn` inside
    /// is the method's contract and proof. A trait method is named by its
    /// type, as the imported function is.
    #[inline(never)]
    pub(super) fn parse_rust_impl_block(
        &mut self,
        function_blocks: &mut Vec<FunctionBlock>,
    ) -> Result<(), ClickError> {
        self.expect_ident_spelling("impl")?;
        // A generic implementation, `impl<T> traits::Keep<T> for Echo`, is
        // verified once for every type: its type parameters are abstract
        // types in the block.
        let generic = self.parse_rust_type_arguments()?;
        let previous_abstract = std::mem::replace(
            &mut self.rust_abstract_type_parameters,
            generic.iter().cloned().collect(),
        );
        let result = self.parse_rust_impl_block_after_generics(function_blocks);
        self.rust_abstract_type_parameters = previous_abstract;
        result
    }

    fn parse_rust_impl_block_after_generics(
        &mut self,
        function_blocks: &mut Vec<FunctionBlock>,
    ) -> Result<(), ClickError> {
        let mut impl_path = self.expect_rust_path("type name")?;
        // A crate trait's instance, `traits::Scale<i32>`, is named with its
        // type arguments; the standard library's operator traits take one.
        let instance = if impl_path.len() > 1 {
            self.parse_rust_type_arguments()?
        } else {
            Vec::new()
        };
        let suffix = self.parse_rust_trait_argument()?;
        let mut inherent = true;
        // A crate trait is named by its path, as a crate type is; the
        // standard library's traits by their own names.
        let mut impl_trait = None;
        if self.peek_ident() == Some("for") {
            self.position += 1;
            if suffix.is_none() && impl_path.len() > 1 {
                impl_trait = Some(trait_instance_name(&impl_path, &instance));
            }
            impl_path = self.expect_rust_path("type name")?;
            inherent = false;
        } else if suffix.is_some() || !instance.is_empty() {
            return Err(self.error("a trait with a type argument is implemented `for` a type"));
        }
        self.expect(Token::LBrace)?;
        let segments: Vec<&str> = impl_path.iter().map(String::as_str).collect();
        let impl_type = crate::languages::rust::names::path_name(&segments);
        // An inherent block is taken to be in its type's module.
        let impl_module = (inherent && segments.len() > 1).then(|| {
            segments[..segments.len() - 1]
                .iter()
                .fold("__rust_q".to_string(), |encoded, segment| {
                    format!("{encoded}_I{}_{segment}", segment.len())
                })
        });
        let suffix = suffix.map(|(reference, mutable, name)| {
            let name = if name == "Self" {
                impl_type.clone()
            } else {
                name
            };
            let scalar = matches!(
                name.as_str(),
                "i32" | "u8" | "u16" | "u32" | "usize" | "bool"
            );
            match (reference, scalar) {
                (false, true) => name,
                (false, false) => format!("value_{}{name}", name.len()),
                (true, _) => format!("ref_{}{name}", if mutable { "mut_" } else { "" }),
            }
        });
        let previous = self.rust_impl_type.replace(impl_type);
        let previous_trait = std::mem::replace(&mut self.rust_impl_trait, impl_trait);
        let previous_suffix = std::mem::replace(&mut self.rust_impl_method_suffix, suffix);
        let previous_module = std::mem::replace(&mut self.rust_impl_module, impl_module);
        let mut result = Ok(());
        while self.peek() != Some(&Token::RBrace) {
            if self.peek_ident() != Some("fn") {
                result = Err(self.error("an `impl` block holds `fn` contracts"));
                break;
            }
            // The method's own name, which names its interface in the trait.
            let method = match self.tokens.get(self.position + 1) {
                Some(Token::Ident(method)) => Some(method.clone()),
                _ => None,
            };
            match self.parse_function_block(false) {
                Ok(block) => {
                    if let (Some(trait_name), Some(method)) = (&self.rust_impl_trait, method)
                        && !self.rust_object_traits.contains(trait_name)
                    {
                        let mut interface = trait_name.clone();
                        crate::languages::rust::names::push_path_segment(&mut interface, &method);
                        self.rust_trait_implementations
                            .push((block.signature().name().to_string(), interface));
                    }
                    function_blocks.push(block)
                }
                Err(error) => {
                    result = Err(error);
                    break;
                }
            }
        }
        self.rust_impl_type = previous;
        self.rust_impl_trait = previous_trait;
        self.rust_impl_method_suffix = previous_suffix;
        self.rust_impl_module = previous_module;
        result?;
        self.expect(Token::RBrace)?;
        Ok(())
    }

    /// Whether `clause` is the object a trait method's receiver holds, which
    /// the token rewrite gives a trait whose object carries state.
    fn is_object_handle(&self, clause: &ResourceClause) -> bool {
        let Some(trait_name) = &self.rust_trait_interface else {
            return false;
        };
        let ResourceClause::Named { resource, .. } = clause else {
            return false;
        };
        matches!(resource.as_ref(), ResourceClause::Declared { name, .. }
            if *name == rust_trait_objects::object_family(trait_name))
    }

    /// `trait traits::Shape { ... }`: each `fn` inside is the interface of
    /// that method of the crate trait, whose contract every implementation
    /// must refine and a call through the trait assumes. A required method's
    /// is an external declaration; a default method's is written with the
    /// proof of its default body.
    #[inline(never)]
    pub(super) fn parse_rust_trait_block(
        &mut self,
        function_blocks: &mut Vec<FunctionBlock>,
    ) -> Result<(), ClickError> {
        self.expect_ident_spelling("trait")?;
        let path = self.expect_rust_path("trait name")?;
        if path.len() < 2 {
            return Err(self.error(
                "a crate trait is named by its path, as the crate writes it: `trait crate_name::Shape`",
            ));
        }
        let arguments = self.parse_rust_type_arguments()?;
        let interface = trait_instance_name(&path, &arguments);
        // A block naming the trait's type parameters is the generic block,
        // read once with each parameter an abstract type; one naming scalar
        // types is an instance's. The token pass has written each instance
        // out already.
        let scalars = arguments
            .iter()
            .filter(|argument| {
                super::rust_generic_traits::INSTANCE_SCALARS.contains(&argument.as_str())
            })
            .count();
        if scalars != 0 && scalars != arguments.len() {
            return Err(self.error(
                "a crate trait's `trait` block names its type parameters, `trait crate_name::Scale<T>`, or an instance's scalar types, `trait crate_name::Scale<i32>`",
            ));
        }
        let abstract_parameters = if scalars == 0 {
            arguments.iter().cloned().collect()
        } else {
            BTreeSet::new()
        };
        let previous_abstract =
            std::mem::replace(&mut self.rust_abstract_type_parameters, abstract_parameters);
        self.expect(Token::LBrace)?;
        let previous = self.rust_trait_interface.replace(interface);
        let mut result = Ok(());
        while self.peek() != Some(&Token::RBrace) {
            if self.peek_ident() != Some("fn") {
                result = Err(self.error("a `trait` block holds `fn` interfaces"));
                break;
            }
            // A default method, written with its proof, is the function its
            // default body defines; the others are external interfaces.
            let has_body = self.rust_trait_method_has_proof();
            match self.parse_function_block(!has_body) {
                // Nor does it hold any of the receiver's resources.
                Ok(block)
                    if block.requires().iter().any(|requirement| {
                        matches!(requirement, Requirement::Resource(clause)
                            if !self.is_object_handle(clause))
                    }) || block.ensures().iter().any(|clause| {
                        matches!(clause.ensure(), Ensure::Resource(resource)
                                if !self.is_object_handle(resource))
                    }) =>
                {
                    result = Err(self.error(
                        "a trait method's interface holds no resources: it reads nothing through `self`, whose type it does not know",
                    ));
                    break;
                }
                Ok(block) => function_blocks.push(block),
                Err(error) => {
                    result = Err(error);
                    break;
                }
            }
        }
        self.rust_trait_interface = previous;
        self.rust_abstract_type_parameters = previous_abstract;
        result?;
        self.expect(Token::RBrace)?;
        Ok(())
    }

    /// A generic crate trait's or a path's type arguments, `<i32>` or `<T,
    /// U>`, each a name; none when no `<` follows.
    pub(super) fn parse_rust_type_arguments(&mut self) -> Result<Vec<String>, ClickError> {
        let mut arguments = Vec::new();
        if self.peek() != Some(&Token::LessThan) {
            return Ok(arguments);
        }
        self.position += 1;
        loop {
            arguments.push(self.expect_ident("type argument")?);
            match self.peek() {
                Some(Token::Comma) => self.position += 1,
                _ => break,
            }
        }
        // `>>` closes this list and the one around it, `<S: traits::Scale<i32>>`.
        if self.peek() == Some(&Token::ShiftRight) {
            self.tokens[self.position] = Token::GreaterThan;
            return Ok(arguments);
        }
        self.expect(Token::GreaterThan)?;
        Ok(arguments)
    }

    /// Whether the trait method at the parser's position is written with a
    /// proof, `fn twice(&self) -> i32 { ... } by { ... }`: the clause block,
    /// the first brace outside the signature's parentheses, is followed by
    /// `by`.
    fn rust_trait_method_has_proof(&self) -> bool {
        let mut parentheses = 0usize;
        let mut index = self.position;
        while let Some(token) = self.tokens.get(index) {
            match token {
                Token::LParen => parentheses += 1,
                Token::RParen => parentheses = parentheses.saturating_sub(1),
                Token::LBrace if parentheses == 0 => break,
                Token::Semicolon | Token::RBrace if parentheses == 0 => return false,
                _ => {}
            }
            index += 1;
        }
        let mut braces = 0usize;
        while let Some(token) = self.tokens.get(index) {
            match token {
                Token::LBrace => braces += 1,
                Token::RBrace => {
                    braces -= 1;
                    if braces == 0 {
                        return matches!(self.tokens.get(index + 1), Some(Token::Ident(word)) if word == "by");
                    }
                }
                _ => {}
            }
            index += 1;
        }
        false
    }

    /// The imported function an inherent method of a type named by a path
    /// is. The importer names it by the module its `impl` block is in,
    /// which Rust does not write, so the one imported function that is this
    /// method of this type is found by the rest of its name. Rust allows a
    /// type one inherent method of a name, so there is at most one. With
    /// no import to consult, or none found, the block is taken to be in its
    /// type's module.
    #[inline(never)]
    pub(super) fn rust_inherent_method(
        &self,
        impl_type: &str,
        method: &str,
    ) -> Result<String, ClickError> {
        let Some(module) = self.rust_impl_module.as_deref() else {
            return Ok(crate::languages::rust::names::inherent_method_name(
                None, impl_type, method,
            ));
        };
        let suffix =
            crate::languages::rust::names::inherent_method_name(Some(""), impl_type, method);
        let mut found = self
            .local_struct_pointers_by_function
            .keys()
            .filter(|name| name.starts_with("__rust_q") && name.ends_with(&suffix));
        match (found.next(), found.next()) {
            (Some(name), None) => Ok(name.clone()),
            (Some(_), Some(_)) => Err(self.error(format!(
                "the import has more than one method `{method}` of this type"
            ))),
            (None, _) => Ok(crate::languages::rust::names::inherent_method_name(
                Some(module),
                impl_type,
                method,
            )),
        }
    }

    /// A Rust path, `name` or `crate_name::module::name`, as its segments.
    #[inline(never)]
    pub(super) fn expect_rust_path(&mut self, what: &str) -> Result<Vec<String>, ClickError> {
        let mut segments = vec![self.expect_ident(what)?];
        while self.peek() == Some(&Token::ColonColon) {
            self.position += 1;
            segments.push(self.expect_ident(what)?);
        }
        Ok(segments)
    }

    /// A Rust path as the name the importer gives the item it names.
    #[inline(never)]
    pub(super) fn expect_rust_path_name(&mut self, what: &str) -> Result<String, ClickError> {
        let path = self.expect_rust_path(what)?;
        Ok(crate::languages::rust::names::path_name(
            &path.iter().map(String::as_str).collect::<Vec<_>>(),
        ))
    }

    /// A lifetime, `'a` in `&'a T`, which a contract does not use.
    pub(super) fn skip_rust_lifetime(&mut self) {
        if matches!(self.peek(), Some(Token::Lifetime(_))) {
            self.position += 1;
        }
    }

    /// The generic parameters after a function's name: lifetimes, `<'a, 'b:
    /// 'a>`, which a contract does not use, and callable type parameters,
    /// `<F: Fn(i32) -> i32>`, by name. The importer refuses other generic
    /// functions, so other type parameters are refused here too.
    #[allow(clippy::type_complexity)]
    pub(super) fn parse_rust_generic_parameters(
        &mut self,
    ) -> Result<BTreeMap<String, (C0Type, syntax::C0FunctionPointerSignature)>, ClickError> {
        let mut callable = BTreeMap::new();
        if self.peek() != Some(&Token::LessThan) {
            return Ok(callable);
        }
        self.position += 1;
        loop {
            // A type parameter bound by nothing a proof reads, `T` or `T:
            // Copy`, is an abstract type: the function is verified once for
            // every type.
            if let Some(word) = self.peek_ident()
                && word != "Fn"
                && (matches!(self.peek_next(), Some(Token::Comma | Token::GreaterThan))
                    || self.peek_next() == Some(&Token::Colon)
                        && matches!(
                            self.tokens.get(self.position + 2),
                            Some(Token::Ident(bound)) if bound == "Copy" || bound == "Clone"
                        ))
            {
                let name = word.to_string();
                self.position += 1;
                if self.peek() == Some(&Token::Colon) {
                    self.position += 1;
                    loop {
                        match self.peek_ident() {
                            Some("Copy" | "Clone") => self.position += 1,
                            _ => {
                                return Err(self.error(
                                    "an abstract type parameter's bounds are `Copy` and `Clone`",
                                ));
                            }
                        }
                        if self.peek() != Some(&Token::Plus) {
                            break;
                        }
                        self.position += 1;
                    }
                }
                if callable.contains_key(&name)
                    || self.rust_trait_type_parameters.contains(&name)
                    || !self.rust_abstract_type_parameters.insert(name)
                {
                    return Err(self.error("a type parameter is declared twice"));
                }
                if self.peek() == Some(&Token::Comma) {
                    self.position += 1;
                }
                if self.peek() == Some(&Token::GreaterThan) {
                    self.position += 1;
                    return Ok(callable);
                }
                continue;
            }
            if let Some(word) = self.peek_ident()
                && self.peek_next() == Some(&Token::Colon)
            {
                let name = word.to_string();
                self.position += 2;
                // `T: traits::Shape`: a crate trait, named by its path.
                if self.peek_ident() != Some("Fn") && self.peek_next() == Some(&Token::ColonColon) {
                    self.expect_rust_path("trait name")?;
                    self.parse_rust_type_arguments()?;
                    if callable.contains_key(&name) || !self.rust_trait_type_parameters.insert(name)
                    {
                        return Err(self.error("a type parameter is declared twice"));
                    }
                    if self.peek() == Some(&Token::Comma) {
                        self.position += 1;
                    }
                    if self.peek() == Some(&Token::GreaterThan) {
                        self.position += 1;
                        return Ok(callable);
                    }
                    continue;
                }
                if self.peek_ident() != Some("Fn") {
                    return Err(self.error(
                        "a `fn` signature's type parameter is supported only with an `Fn(...) -> ...` bound or a crate trait's, such as `<T: crate_name::Shape>`",
                    ));
                }
                self.position += 1;
                let signature = self.parse_rust_callable_signature()?;
                if callable.insert(name, signature).is_some() {
                    return Err(self.error("a type parameter is declared twice"));
                }
                if self.peek() == Some(&Token::Comma) {
                    self.position += 1;
                }
                if self.peek() == Some(&Token::GreaterThan) {
                    self.position += 1;
                    return Ok(callable);
                }
                continue;
            }
            let Some(Token::Lifetime(_)) = self.peek() else {
                return Err(self.error(
                    "a `fn` signature's generic parameters may only be lifetimes, such as `<'a>`, and `Fn` type parameters, such as `<F: Fn(i32) -> i32>`",
                ));
            };
            self.position += 1;
            if self.peek() == Some(&Token::Colon) {
                self.position += 1;
                while matches!(self.peek(), Some(Token::Lifetime(_))) {
                    self.position += 1;
                    if self.peek() != Some(&Token::Plus) {
                        break;
                    }
                    self.position += 1;
                }
            }
            if self.peek() == Some(&Token::Comma) {
                self.position += 1;
            }
            if self.peek() == Some(&Token::GreaterThan) {
                self.position += 1;
                return Ok(callable);
            }
        }
    }

    /// The type argument of an operator trait, `<u32>`, `<&Lanes>` or
    /// `<Self>`: whether it is a reference, whether that is mutable, and
    /// the type's name. The caller turns it into the suffix the Rust
    /// importer gives the implementation's methods (`rhs_name` in
    /// `src/languages/rust/charon/assignment_operators.rs`): a scalar by its
    /// name, a record by value as `value_<length><name>`, and a reference as
    /// `ref_` or `ref_mut_` and what it refers to. `None`, with nothing
    /// consumed, for a trait without one.
    #[inline(never)]
    pub(super) fn parse_rust_trait_argument(
        &mut self,
    ) -> Result<Option<(bool, bool, String)>, ClickError> {
        if self.peek() != Some(&Token::LessThan) {
            return Ok(None);
        }
        self.position += 1;
        let reference = self.peek() == Some(&Token::Amp);
        if reference {
            self.position += 1;
            self.skip_rust_lifetime();
        }
        let mutable = reference && self.peek_ident() == Some("mut");
        if mutable {
            self.position += 1;
        }
        let name = self.expect_rust_path_name("type name")?;
        self.expect(Token::GreaterThan)?;
        Ok(Some((reference, mutable, name)))
    }

    /// A method's receiver: `&self`, `&mut self` or `self`, as the type of
    /// the parameter it is. `None`, with nothing consumed, for an associated
    /// function that takes no receiver.
    pub(super) fn parse_rust_receiver(
        &mut self,
        impl_type: &str,
    ) -> Result<Option<ParsedType>, ClickError> {
        let start = self.position;
        let reference = self.peek() == Some(&Token::Amp);
        if reference {
            self.position += 1;
            self.skip_rust_lifetime();
        }
        let mutable = reference && self.peek_ident() == Some("mut");
        if mutable {
            self.position += 1;
        }
        if self.peek_ident() != Some("self") {
            self.position = start;
            return Ok(None);
        }
        self.position += 1;
        Ok(Some(ParsedType {
            c_type: C0Type::Int32Pointer,
            struct_name: Some(impl_type.to_string()),
            struct_pointer: reference,
            constant: false,
            pointee_constant: reference && !mutable,
            reference: false,
        }))
    }

    /// `&[T]` or `&mut [T]` with a scalar element, as the pointer to its
    /// first element; `None`, with nothing consumed, for any other type.
    #[inline(never)]
    pub(super) fn parse_rust_slice_type(&mut self) -> Result<Option<ParsedType>, ClickError> {
        if self.peek() != Some(&Token::Amp) {
            return Ok(None);
        }
        let lifetime = usize::from(matches!(self.peek_next(), Some(Token::Lifetime(_))));
        let mutable =
            self.tokens.get(self.position + 1 + lifetime) == Some(&Token::Ident("mut".into()));
        let bracket = self.position + 1 + lifetime + usize::from(mutable);
        if self.tokens.get(bracket) != Some(&Token::LBracket) {
            return Ok(None);
        }
        // `&[T; N]` is a reference to an array, not a slice.
        if self.tokens.get(bracket + 2) == Some(&Token::Semicolon) {
            return Ok(None);
        }
        self.position = bracket + 1;
        let spelling = self.expect_ident("slice element type")?;
        let Some(c_type) = rust_scalar_type(&spelling).and_then(C0Type::pointer_type) else {
            return Err(self.error(format!(
                "a slice of `{spelling}` in a `fn` signature is not supported; the Rust importer reads slices of scalars only"
            )));
        };
        self.expect(Token::RBracket)?;
        Ok(Some(ParsedType {
            c_type,
            struct_name: None,
            struct_pointer: false,
            constant: false,
            pointee_constant: !mutable,
            reference: false,
        }))
    }

    /// `name.len()` where `name` is a slice parameter: consumes `.len()` and
    /// answers the length's own name.
    pub(super) fn take_rust_slice_len(&mut self, name: &str) -> Option<String> {
        if !self.rust_slice_params.contains(name)
            || self.peek() != Some(&Token::Dot)
            || self.peek_next() != Some(&Token::Ident("len".into()))
            || self.tokens.get(self.position + 2) != Some(&Token::LParen)
            || self.tokens.get(self.position + 3) != Some(&Token::RParen)
        {
            return None;
        }
        self.position += 4;
        Some(format!("{name}_len"))
    }

    /// `&T` and `&mut T` in a signature. The parameter is the pointer that
    /// carries the reference, as Rust's own `value` is: the contract names
    /// the referent `*value` and a field `parent.left`. `&T` is a pointer to
    /// a constant referent. The contract still states `views` or `owns`.
    #[inline(never)]
    pub(super) fn parse_rust_reference_type(&mut self) -> Result<ParsedType, ClickError> {
        self.expect(Token::Amp)?;
        self.skip_rust_lifetime();
        let mutable = if self.peek_ident() == Some("mut") {
            self.position += 1;
            true
        } else {
            false
        };
        if matches!(self.peek(), Some(Token::Amp | Token::LParen)) {
            return Err(self.error(
                "a reference to a reference or to `()` in a `fn` signature is not supported; the Rust importer refuses it",
            ));
        }
        // A value of an abstract type parameter is held by value only.
        if matches!(self.peek_ident(), Some(name) if self.rust_abstract_type_parameters.contains(name))
            && !matches!(self.peek_next(), Some(Token::ColonColon))
        {
            return Err(self.error(
                "a reference to a value of an abstract type parameter is not supported; the Rust importer refuses it",
            ));
        }
        // `&dyn traits::Shape`, or `&T` for a crate trait's type parameter:
        // a value of a type the function does not know, whose fields it
        // cannot name.
        let dyn_trait = self.peek_ident() == Some("dyn");
        if dyn_trait {
            self.position += 1;
            self.expect_rust_path("trait name")?;
            self.parse_rust_type_arguments()?;
        }
        if dyn_trait
            || matches!(self.peek_ident(), Some(name) if self.rust_trait_type_parameters.contains(name))
                && !matches!(self.peek_next(), Some(Token::ColonColon))
        {
            if !dyn_trait {
                self.position += 1;
            }
            return Ok(ParsedType {
                c_type: C0Type::Int32Pointer,
                struct_name: None,
                struct_pointer: false,
                constant: false,
                pointee_constant: !mutable,
                reference: false,
            });
        }
        // `&[T; N]` is the pointer to the array's first element. The length
        // is the type's, so the contract writes it: `views words[0..N]`.
        let array = self.peek() == Some(&Token::LBracket);
        if array {
            self.position += 1;
        }
        let spelling = self.expect_rust_path_name("type")?;
        if array {
            self.expect(Token::Semicolon)?;
            // The length is a constant expression; the importer checks it.
            while !matches!(self.peek(), Some(Token::RBracket) | None) {
                self.position += 1;
            }
            self.expect(Token::RBracket)?;
            if rust_scalar_type(&spelling).is_none() {
                return Err(self.error(format!(
                    "an array of `{spelling}` in a `fn` signature is not supported; the Rust importer reads arrays of scalars only"
                )));
            }
        }
        Ok(match rust_scalar_type(&spelling) {
            Some(scalar) => {
                let Some(c_type) = scalar.pointer_type() else {
                    return Err(self.error(format!(
                        "a reference to `{spelling}` is not supported in a `fn` signature"
                    )));
                };
                ParsedType {
                    c_type,
                    struct_name: None,
                    struct_pointer: false,
                    constant: false,
                    pointee_constant: !mutable,
                    reference: false,
                }
            }
            None => ParsedType {
                c_type: C0Type::Int32Pointer,
                struct_name: Some(spelling),
                struct_pointer: true,
                constant: false,
                pointee_constant: !mutable,
                reference: false,
            },
        })
    }

    /// A Rust type in a signature: an integer or float type, `bool`, `()`,
    /// or a struct by name.
    /// A function-pointer type, `fn(i32, u32) -> bool`, of scalar parameters
    /// and a scalar or unit result.
    /// A `&dyn Fn(i32) -> i32`, a callable value of the same type as the
    /// `fn` pointer of its parameters and result.
    fn parse_rust_dyn_fn_type(
        &mut self,
    ) -> Result<(C0Type, syntax::C0FunctionPointerSignature), ClickError> {
        self.expect(Token::Amp)?;
        self.skip_rust_lifetime();
        self.expect_ident_spelling("dyn")?;
        if self.peek_ident() != Some("Fn") {
            return Err(self.error("a `&dyn` parameter is supported only for `Fn(...) -> ...`"));
        }
        self.position += 1;
        self.parse_rust_callable_signature()
    }

    /// An `impl Fn(i32) -> i32`, a callable value as `&dyn Fn` is.
    fn parse_rust_impl_fn_type(
        &mut self,
    ) -> Result<(C0Type, syntax::C0FunctionPointerSignature), ClickError> {
        self.expect_ident_spelling("impl")?;
        if self.peek_ident() != Some("Fn") {
            return Err(self.error("an `impl` parameter is supported only for `Fn(...) -> ...`"));
        }
        self.position += 1;
        self.parse_rust_callable_signature()
    }

    fn parse_rust_fn_pointer_type(
        &mut self,
    ) -> Result<(C0Type, syntax::C0FunctionPointerSignature), ClickError> {
        self.expect_ident_spelling("fn")?;
        self.parse_rust_callable_signature()
    }

    /// The parameter list and result of a callable type, after `fn` or `Fn`.
    fn parse_rust_callable_signature(
        &mut self,
    ) -> Result<(C0Type, syntax::C0FunctionPointerSignature), ClickError> {
        self.expect(Token::LParen)?;
        let mut parameters = Vec::new();
        while self.peek() != Some(&Token::RParen) {
            let parsed = self.parse_rust_type()?;
            if parsed.c_type == C0Type::Void || parsed.c_type.is_pointer() || parsed.reference {
                return Err(self.error("a `fn` pointer type takes scalar parameters"));
            }
            parameters.push(syntax::C0FunctionPointerParameter::new(
                parsed.c_type,
                None,
                false,
            ));
            if self.peek() != Some(&Token::Comma) {
                break;
            }
            self.position += 1;
        }
        self.expect(Token::RParen)?;
        let result = if self.peek() == Some(&Token::Arrow) {
            self.position += 1;
            let parsed = self.parse_rust_type()?;
            if parsed.c_type.is_pointer() || parsed.reference {
                return Err(self.error("a `fn` pointer type returns a scalar or `()`"));
            }
            parsed.c_type
        } else {
            C0Type::Void
        };
        let signature = syntax::C0FunctionPointerSignature::new(result, None, parameters, false);
        Ok((signature.pointer_type(), signature))
    }

    pub(super) fn parse_rust_type(&mut self) -> Result<ParsedType, ClickError> {
        let scalar = |c_type| ParsedType {
            c_type,
            struct_name: None,
            struct_pointer: false,
            constant: false,
            pointee_constant: false,
            reference: false,
        };
        if self.peek() == Some(&Token::LParen) {
            self.position += 1;
            self.expect(Token::RParen)?;
            return Ok(scalar(C0Type::Void));
        }
        if self.peek() == Some(&Token::Amp) {
            return self.parse_rust_reference_type();
        }
        if self.peek() == Some(&Token::LBracket) {
            return Err(self.error(
                "an array or slice passed by value in a `fn` signature is not supported; the Rust importer refuses it",
            ));
        }
        if let Some(name) = self.peek_ident()
            && self.rust_abstract_type_parameters.contains(name)
            && self.peek_next() != Some(&Token::ColonColon)
        {
            let parameter = crate::kernel::TypeParameterName::intern(name);
            self.position += 1;
            return Ok(scalar(C0Type::Parameter(parameter)));
        }
        let spelling = self.expect_rust_path_name("type")?;
        Ok(match rust_scalar_type(&spelling) {
            Some(c_type) => scalar(c_type),
            None => ParsedType {
                c_type: C0Type::Int32Pointer,
                struct_name: Some(spelling),
                struct_pointer: false,
                constant: false,
                pointee_constant: false,
                reference: false,
            },
        })
    }

    /// The type of a Click binder in a Rust sidecar, spelled as Rust does:
    /// a scalar (`u8`, `i32`, `usize`, `bool`, ...) or a raw pointer to one
    /// or to a crate struct, `*const T` or `*mut T`. A pure function, predicate or theorem takes
    /// values: a fn's slice `bytes` passes the pointer to its first element,
    /// so a function over its bytes takes `bytes: *const u8` and a `usize`
    /// length. `None`, with nothing consumed, for anything else, which the
    /// shared spellings read.
    #[inline(never)]
    pub(super) fn parse_rust_click_type(&mut self) -> Result<Option<ParsedType>, ClickError> {
        if !self.verifies_rust() {
            return Ok(None);
        }
        if self.peek() == Some(&Token::Amp) {
            return Err(self.error(
                "a pure function, predicate or theorem takes values, not references; write a pointer `*const T` or `*mut T`, and pass a slice as its pointer and a `usize` length",
            ));
        }
        let scalar = |c_type, pointee_constant| ParsedType {
            c_type,
            struct_name: None,
            struct_pointer: false,
            constant: false,
            pointee_constant,
            reference: false,
        };
        if self.peek() == Some(&Token::Star) {
            let mutable = match self.peek_next() {
                Some(Token::Ident(word)) if word == "const" => false,
                Some(Token::Ident(word)) if word == "mut" => true,
                _ => return Err(self.error("a Rust pointer type is `*const T` or `*mut T`")),
            };
            self.position += 2;
            // A raw pointer to a crate struct, `*const crate::S`, as a
            // `fn` signature reads its references to one.
            if self
                .peek_ident()
                .is_some_and(|word| rust_scalar_type(word).is_none())
            {
                let spelling = self.expect_rust_path_name("pointee type")?;
                return Ok(Some(ParsedType {
                    c_type: C0Type::Int32Pointer,
                    struct_name: Some(spelling),
                    struct_pointer: true,
                    constant: false,
                    pointee_constant: !mutable,
                    reference: false,
                }));
            }
            let spelling = self.expect_ident("pointee type")?;
            let Some(c_type) = rust_scalar_type(&spelling)
                .filter(|pointee| *pointee != C0Type::Bool)
                .and_then(C0Type::pointer_type)
            else {
                return Err(self.error(format!(
                    "a pointer to `{spelling}` is not a Click binder type; a Rust sidecar's binder may point at an integer or float scalar"
                )));
            };
            return Ok(Some(scalar(c_type, !mutable)));
        }
        let Some(c_type) = self.peek_ident().and_then(rust_scalar_type) else {
            return Ok(None);
        };
        self.position += 1;
        Ok(Some(scalar(c_type, false)))
    }

    /// `expr as T` in a Rust sidecar is the scalar cast `(T)expr`. It binds
    /// tighter than a binary operator and looser than a unary one, as in
    /// Rust. `as` followed by anything but a scalar type is left for the
    /// clause that owns it (`intro() as name`).
    #[inline(never)]
    pub(super) fn parse_rust_casts(
        &mut self,
        mut operand: ContractExpression,
    ) -> Result<ContractExpression, ClickError> {
        while self.verifies_rust()
            && self.peek_ident() == Some("as")
            && matches!(
                self.peek_next(),
                Some(Token::Ident(name)) if rust_scalar_type(name).is_some()
            )
        {
            self.position += 1;
            let target = self.expect_ident("type")?;
            if target == "bool" {
                return Err(self
                    .error("Rust does not cast to `bool`; compare with zero instead, `(x != 0)`"));
            }
            let target_type = rust_scalar_type(&target)
                .expect("checked above")
                .to_kernel_type();
            let Some(expression) = contract_expression_as_c_fragment(&operand) else {
                return Err(self.error("scalar cast expects a current C expression; put old(...) around the whole cast for an entry-state value"));
            };
            // Keep the same operand-bearing representation as a C-style
            // scalar cast, including its proof-expression identity.
            operand = ContractExpression::CUnary {
                operand: Box::new(operand),
                lowered: CExpression::Cast {
                    expression: Box::new(expression),
                    target_type,
                    integer_mode: crate::kernel::CIntegerCastMode::CConversion,
                    pointee_struct: None,
                    pointee_volatile: false,
                    pointee_constant: false,
                    explicit_qualification: false,
                },
            };
        }
        Ok(operand)
    }
}

/// The C0 type a Rust scalar type name denotes.
fn rust_scalar_type(name: &str) -> Option<C0Type> {
    Some(match name {
        "bool" => C0Type::Bool,
        "i8" => C0Type::Int8,
        "i16" => C0Type::Int16,
        "i32" => C0Type::Int32,
        "i64" | "isize" => C0Type::Int64(LongRank::Long),
        "i128" => C0Type::Int128,
        "u8" => C0Type::UInt8,
        "u16" => C0Type::UInt16,
        "u32" => C0Type::UInt32,
        "u64" | "usize" => C0Type::UInt64(LongRank::Long),
        "u128" => C0Type::UInt128,
        "f32" => C0Type::Float32,
        "f64" => C0Type::Float64,
        _ => return None,
    })
}

pub(super) fn rust_signature_hint(parsed: &ParsedFunctionSignature) -> Option<String> {
    let signature = &parsed.signature;
    if !parsed.struct_params.is_empty() || parsed.return_struct_name.is_some() {
        return None;
    }
    let scalar_name = |c_type| {
        [
            "bool", "i8", "i16", "i32", "isize", "i128", "u8", "u16", "u32", "usize", "u128",
            "f32", "f64",
        ]
        .into_iter()
        .find(|name| rust_scalar_type(name) == Some(c_type))
    };
    let name = crate::languages::rust::names::rust_display_name(&signature.name)
        .unwrap_or_else(|| signature.name.clone());
    // An importer name that is no path, or an operator method's qualified
    // form, has no `fn` spelling.
    if name.starts_with("__rust_q") || name.starts_with('<') {
        return None;
    }
    let mut parameters = Vec::new();
    let mut index = 0;
    while let Some(parameter) = signature.parameters.get(index) {
        let spelling = if let Some(pointee) = parameter.c_type().pointee_type() {
            let reference = if parameter.pointee_constant {
                "&"
            } else {
                "&mut "
            };
            let base = scalar_name(pointee)?;
            let slice = signature.parameters.get(index + 1).is_some_and(|length| {
                length.name == format!("{}_len", parameter.name)
                    && matches!(length.c_type(), C0Type::UInt64(_))
            });
            if slice {
                index += 1;
                format!("{reference}[{base}]")
            } else {
                format!("{reference}{base}")
            }
        } else {
            scalar_name(parameter.c_type())?.to_string()
        };
        parameters.push(format!("{}: {spelling}", parameter.name));
        index += 1;
    }
    let return_type = if signature.return_type == C0Type::Void {
        String::new()
    } else {
        format!(" -> {}", scalar_name(signature.return_type)?)
    };
    Some(format!("fn {name}({}){return_type}", parameters.join(", ")))
}
