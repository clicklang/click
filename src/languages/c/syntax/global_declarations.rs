//! Parsing file-scope declarations: global scalars, arrays and aggregates, their initializers and inferred lengths, and their registration.

use super::*;

impl Parser {
    pub(super) fn global_declaration_ahead(&mut self) -> Result<bool, C0SyntaxError> {
        let saved_position = self.position;
        if self.peek_ident() == Some("extern") {
            self.position += 1;
        }
        if !self.is_type_start() {
            self.position = saved_position;
            return Ok(false);
        }
        // Lookahead must recognize declaration-only return types without
        // granting their value semantics. The actual object/header parser
        // still decides whether that type is permitted at the chosen site.
        self.parse_type_with_anonymous_struct(false, true, true)?;
        let is_global =
            matches!(self.peek(), Some(Token::Ident(_))) && self.peek_n(1) != Some(&Token::LParen);
        self.position = saved_position;
        Ok(is_global)
    }

    pub(super) fn parse_global_declaration(&mut self) -> Result<(), C0SyntaxError> {
        let is_file_static = if self.peek_ident() == Some("static") {
            self.position += 1;
            true
        } else {
            false
        };
        let is_extern = if self.peek_ident() == Some("extern") {
            self.position += 1;
            true
        } else {
            false
        };
        if is_file_static && is_extern {
            return Err(self.error_here(
                "file-scope declarations may use either `static` or `extern`, not both",
            ));
        }
        let parsed_type = self.parse_type()?;
        if parsed_type.function_pointer_signature.is_some() {
            return Err(self.error_here("global function-pointer objects are not supported"));
        }
        let struct_pointer_name = parsed_type
            .struct_name
            .as_ref()
            .filter(|_| parsed_type.c_type.is_pointer())
            .cloned();
        if let Some(struct_name) = &struct_pointer_name
            && !self.structs.contains_key(struct_name)
        {
            return Err(self.error_here(format!("unknown struct declaration `{struct_name}`")));
        }
        let aggregate_struct = if is_plain_struct_type(&parsed_type) {
            if parsed_type.is_volatile {
                return Err(self.error_here(
                    "the small volatile model does not support volatile aggregate globals",
                ));
            }
            let struct_name = parsed_type
                .struct_name
                .clone()
                .expect("plain struct global carries a struct name");
            let layout = self.scalar_struct_value_layout(&struct_name)?;
            Some((struct_name, layout))
        } else {
            self.validate_volatile_type(&parsed_type)?;
            if (parsed_type.struct_name.is_some() && struct_pointer_name.is_none())
                || parsed_type.enum_name.is_some()
                || parsed_type.union_name.is_some()
                || (struct_pointer_name.is_none()
                    && !parsed_type.c_type.is_supported_static_scalar())
            {
                return Err(self.error_here(
                    "file-scope declarations currently support only scalar integer, floating-point, struct-pointer, or supported struct globals",
                ));
            }
            None
        };
        if self.header_mode && !is_extern {
            return Err(self.error_here(
                "C headers may declare globals only with `extern`; put the definition in a source file",
            ));
        }

        loop {
            let name = self.expect_ident("global name")?;
            let kernel_name = if is_file_static {
                self.file_static_kernel_name(&name)
            } else {
                name.clone()
            };
            if let Some((struct_name, layout)) = &aggregate_struct {
                if self.peek() == Some(&Token::LBracket) {
                    let mut array_length = self
                        .parse_global_array_length(&name)?
                        .expect("aggregate array has an array suffix");
                    let mut inferred_initializer = None;
                    if matches!(&array_length, GlobalArrayLength::Incomplete(shape) if shape.is_empty())
                        && !is_extern
                        && self.peek() == Some(&Token::Equal)
                    {
                        self.position += 1;
                        let (length, initializer) = self
                            .parse_aggregate_array_initializer_with_bound(
                                &name,
                                struct_name,
                                layout,
                                None,
                            )?;
                        array_length = GlobalArrayLength::Complete(vec![length]);
                        inferred_initializer = Some(initializer);
                    }
                    let declaration = match array_length {
                        GlobalArrayLength::Complete(shape) => {
                            if shape.len() != 1 {
                                return Err(self.error_here(
                                    "multidimensional aggregate arrays are not supported yet",
                                ));
                            }
                            let length = shape[0];
                            let has_initializer = inferred_initializer.is_some()
                                || self.peek() == Some(&Token::Equal);
                            let initializer = if let Some(initializer) = inferred_initializer {
                                Some(initializer)
                            } else if has_initializer {
                                if is_extern {
                                    return Err(self.error_here(
                                        "`extern` aggregate global array declarations may not have an initializer",
                                    ));
                                }
                                self.position += 1;
                                Some(self.parse_aggregate_array_initializer(
                                    &name,
                                    struct_name,
                                    layout,
                                    length,
                                )?)
                            } else if is_extern {
                                None
                            } else {
                                Some(Vec::new())
                            };
                            let tentative = !has_initializer && !is_extern;
                            initializer
                                .map(|initializer| {
                                    C0GlobalAggregateArray::definition(
                                        name.clone(),
                                        kernel_name.clone(),
                                        struct_name.clone(),
                                        layout.clone(),
                                        length,
                                        initializer,
                                        is_file_static,
                                    )
                                })
                                .unwrap_or_else(|| {
                                    C0GlobalAggregateArray::declaration(
                                        name.clone(),
                                        kernel_name.clone(),
                                        struct_name.clone(),
                                        layout.clone(),
                                        Some(length),
                                        is_file_static,
                                    )
                                })
                                .with_constant(parsed_type.is_constant)
                                .with_tentative(tentative)
                        }
                        GlobalArrayLength::Incomplete(incomplete_shape) => {
                            if !incomplete_shape.is_empty() {
                                return Err(self.error_here(
                                    "incomplete multidimensional aggregate arrays are not supported yet",
                                ));
                            }
                            if !is_extern {
                                return Err(self.error_here(
                                    "incomplete aggregate array definitions are not supported yet",
                                ));
                            }
                            if self.peek() == Some(&Token::Equal) {
                                return Err(self.error_here(
                                    "incomplete external aggregate array declarations may not have an initializer",
                                ));
                            }
                            C0GlobalAggregateArray::declaration(
                                name.clone(),
                                kernel_name.clone(),
                                struct_name.clone(),
                                layout.clone(),
                                None,
                                is_file_static,
                            )
                            .with_constant(parsed_type.is_constant)
                        }
                    };
                    self.register_global_aggregate_array_declaration(name.clone(), declaration)?;
                    if let Some(length) = self
                        .global_aggregate_arrays
                        .get(&name)
                        .and_then(C0GlobalAggregateArray::array_length)
                    {
                        let bytes = length
                            .checked_mul(layout.size_bytes())
                            .expect("validated aggregate global array size");
                        self.variable_types
                            .insert(kernel_name.clone(), C0Type::UInt8Array(bytes));
                        self.variable_array_shapes
                            .insert(kernel_name.clone(), vec![length]);
                        self.incomplete_array_names.remove(&kernel_name);
                    } else {
                        self.variable_types
                            .insert(kernel_name.clone(), C0Type::UInt8Pointer);
                        self.variable_array_shapes.remove(&kernel_name);
                        self.incomplete_array_names.insert(kernel_name.clone());
                    }
                    self.variable_structs
                        .insert(kernel_name.clone(), struct_name.clone());
                    if parsed_type.is_constant {
                        self.variable_constants.insert(kernel_name.clone());
                    }
                    if self.peek() == Some(&Token::Comma) {
                        self.position += 1;
                        continue;
                    }
                    break;
                }
                let has_initializer = self.peek() == Some(&Token::Equal);
                let initializer = if has_initializer {
                    if is_extern {
                        return Err(self.error_here(
                            "`extern` aggregate global declarations may not have an initializer",
                        ));
                    }
                    self.position += 1;
                    Some(self.parse_aggregate_initializer(&name, struct_name)?)
                } else if is_extern {
                    None
                } else {
                    Some(Vec::new())
                };
                let tentative = !has_initializer && !is_extern;
                let declaration = if let Some(initializer) = initializer {
                    C0GlobalAggregate::definition(
                        name.clone(),
                        kernel_name.clone(),
                        struct_name.clone(),
                        layout.clone(),
                        initializer,
                        is_file_static,
                    )
                } else {
                    C0GlobalAggregate::declaration(
                        name.clone(),
                        kernel_name.clone(),
                        struct_name.clone(),
                        layout.clone(),
                        is_file_static,
                    )
                }
                .with_constant(parsed_type.is_constant);
                let declaration = declaration.with_tentative(tentative);
                self.register_global_aggregate_declaration(name.clone(), declaration)?;
                self.variable_struct_values
                    .insert(kernel_name.clone(), struct_name.clone());
                self.variable_types
                    .insert(name.clone(), struct_value_type(layout));
                self.variable_structs
                    .insert(name.clone(), struct_name.clone());
                if parsed_type.is_constant {
                    self.variable_constants.insert(name.clone());
                }
                if kernel_name != name {
                    self.variable_types
                        .insert(kernel_name.clone(), struct_value_type(layout));
                    self.variable_structs
                        .insert(kernel_name, struct_name.clone());
                }
                if self.peek() == Some(&Token::Comma) {
                    self.position += 1;
                    continue;
                }
                break;
            }
            let parsed_array_length = self.parse_global_array_length(&name)?;
            let mut inferred_initializer = None;
            let mut incomplete_tentative = false;
            let array_length = match parsed_array_length {
                Some(GlobalArrayLength::Incomplete(incomplete_shape)) if !is_extern => {
                    if self.peek() != Some(&Token::Equal) {
                        if !incomplete_shape.is_empty() && is_file_static {
                            return Err(self.error_here(
                                "incomplete multidimensional file-scope static arrays are not supported yet",
                            ));
                        }
                        incomplete_tentative = true;
                        Some(GlobalArrayLength::Incomplete(incomplete_shape))
                    } else if incomplete_shape.is_empty() {
                        self.position += 1;
                        let initializer = self
                            .parse_inferred_global_array_initializer(&name, parsed_type.c_type)?;
                        let length = u32::try_from(initializer.len()).map_err(|_| {
                            self.error_here(format!(
                                "inferred file-scope array `{name}` has too many initializers"
                            ))
                        })?;
                        if length == 0 {
                            return Err(self.error_here(format!(
                                "inferred file-scope array `{name}` requires a non-empty initializer"
                            )));
                        }
                        inferred_initializer =
                            Some(C0ArrayInitializer::dense(parsed_type.c_type, initializer));
                        Some(GlobalArrayLength::Complete(vec![length]))
                    } else {
                        self.position += 1;
                        let (shape, initializer) = self
                            .parse_inferred_multidimensional_global_array_initializer(
                                &name,
                                parsed_type.c_type,
                                &incomplete_shape,
                            )?;
                        inferred_initializer = Some(initializer);
                        Some(GlobalArrayLength::Complete(shape))
                    }
                }
                other => other,
            };
            if array_length.is_some() && array_type_for_element(parsed_type.c_type, 1).is_none() {
                return Err(self.error_here(
                    "file-scope array element type requires a modeled array pointer type",
                ));
            }
            if parsed_type.is_volatile && array_length.is_some() {
                return Err(self.error_here(
                    "the small volatile model supports only direct scalar integer objects",
                ));
            }
            if let Some(array_length) = array_length {
                if let Some(struct_name) = &struct_pointer_name {
                    self.variable_structs
                        .insert(kernel_name.clone(), struct_name.clone());
                }
                match array_length {
                    GlobalArrayLength::Complete(shape) => {
                        // The block's byte size, not only its element count,
                        // must fit the layout width.
                        let length = array_shape_element_count(&shape)
                            .filter(|length| {
                                length
                                    .checked_mul(parsed_type.c_type.abi_size_bytes())
                                    .is_some()
                            })
                            .ok_or_else(|| {
                                self.error_here(format!(
                                    "file-scope array dimensions are too large for `{name}`"
                                ))
                            })?;
                        let has_initializer =
                            inferred_initializer.is_some() || self.peek() == Some(&Token::Equal);
                        let initializer = if has_initializer {
                            if is_extern {
                                return Err(self.error_here(
                                "`extern` global array declarations may not have an initializer",
                            ));
                            }
                            if let Some(initializer) = inferred_initializer {
                                Some(initializer)
                            } else {
                                self.position += 1;
                                Some(self.parse_global_array_initializer(
                                    &name,
                                    parsed_type.c_type,
                                    &shape,
                                )?)
                            }
                        } else if is_extern {
                            None
                        } else {
                            Some(C0ArrayInitializer::zeroed(length, parsed_type.c_type))
                        };
                        let tentative = !has_initializer && !is_extern;
                        self.register_global_array_declaration(
                            name.clone(),
                            parsed_type.c_type,
                            initializer
                                .map(|initializer| {
                                    C0GlobalArray::definition(
                                        name.clone(),
                                        kernel_name.clone(),
                                        parsed_type.c_type,
                                        shape.clone(),
                                        initializer,
                                        is_file_static,
                                    )
                                    .with_constant(parsed_type.is_constant)
                                    .with_tentative(tentative)
                                })
                                .unwrap_or_else(|| {
                                    C0GlobalArray::declaration(
                                        name.clone(),
                                        kernel_name.clone(),
                                        parsed_type.c_type,
                                        Some(shape.clone()),
                                        None,
                                        is_file_static,
                                    )
                                    .with_constant(parsed_type.is_constant)
                                }),
                        )?;
                        self.variable_types.insert(
                            kernel_name.clone(),
                            array_type_for_element(parsed_type.c_type, length)
                                .expect("validated global array element type"),
                        );
                        self.variable_array_shapes
                            .insert(kernel_name.clone(), shape);
                        self.incomplete_array_names.remove(&kernel_name);
                    }
                    GlobalArrayLength::Incomplete(incomplete_shape) => {
                        if self.peek() == Some(&Token::Equal) {
                            return Err(self.error_here(
                                "incomplete external array declarations may not have an initializer",
                            ));
                        }
                        self.register_global_array_declaration(
                            name.clone(),
                            parsed_type.c_type,
                            C0GlobalArray::declaration(
                                name.clone(),
                                kernel_name.clone(),
                                parsed_type.c_type,
                                None,
                                Some(incomplete_shape),
                                is_file_static,
                            )
                            .with_constant(parsed_type.is_constant)
                            .with_tentative(incomplete_tentative),
                        )?;
                        if let Some(shape) = self
                            .global_arrays
                            .get(&name)
                            .and_then(C0GlobalArray::index_shape)
                        {
                            let length = array_shape_element_count(&shape)
                                .expect("validated global array shape");
                            self.variable_types.insert(
                                kernel_name.clone(),
                                array_type_for_element(parsed_type.c_type, length)
                                    .expect("validated global array element type"),
                            );
                            self.variable_array_shapes
                                .insert(kernel_name.clone(), shape);
                            self.incomplete_array_names.remove(&kernel_name);
                        } else {
                            let element_pointer = parsed_type
                                .c_type
                                .pointer_type()
                                .expect("validated incomplete external array element type");
                            self.variable_types
                                .insert(kernel_name.clone(), element_pointer);
                            self.variable_array_shapes.remove(&kernel_name);
                            self.incomplete_array_names.insert(kernel_name.clone());
                        }
                    }
                }
            } else {
                let has_initializer = self.peek() == Some(&Token::Equal);
                let initializer = if has_initializer {
                    if is_extern {
                        return Err(self.error_here(
                            "`extern` global declarations may not have an initializer",
                        ));
                    }
                    self.position += 1;
                    let initializer = self.parse_expression()?;
                    let initializer = normalize_static_initializer(
                        self,
                        parsed_type.c_type,
                        parsed_type.pointee_constant,
                        &initializer,
                        "global",
                        false,
                    )?;
                    Some(initializer)
                } else if is_extern {
                    None
                } else {
                    Some(zero_initializer(parsed_type.c_type))
                };
                let tentative = !has_initializer && !is_extern;
                self.register_global_declaration(
                    name.clone(),
                    parsed_type.c_type,
                    initializer
                        .map(|initializer| {
                            if is_file_static {
                                C0Global::file_static_definition(
                                    name.clone(),
                                    kernel_name.clone(),
                                    parsed_type.c_type,
                                    struct_pointer_name.clone(),
                                    initializer,
                                )
                                .with_volatile(parsed_type.object_is_volatile())
                                .with_pointee_volatile(parsed_type.pointee_is_volatile())
                                .with_constant(parsed_type.is_constant)
                                .with_pointee_constant(parsed_type.pointee_constant)
                                .with_tentative(tentative)
                            } else {
                                C0Global::definition(
                                    name.clone(),
                                    parsed_type.c_type,
                                    struct_pointer_name.clone(),
                                    initializer,
                                )
                                .with_volatile(parsed_type.object_is_volatile())
                                .with_pointee_volatile(parsed_type.pointee_is_volatile())
                                .with_constant(parsed_type.is_constant)
                                .with_pointee_constant(parsed_type.pointee_constant)
                                .with_tentative(tentative)
                            }
                        })
                        .unwrap_or_else(|| {
                            C0Global::declaration(
                                name.clone(),
                                parsed_type.c_type,
                                struct_pointer_name.clone(),
                            )
                            .with_volatile(parsed_type.object_is_volatile())
                            .with_pointee_volatile(parsed_type.pointee_is_volatile())
                            .with_constant(parsed_type.is_constant)
                            .with_pointee_constant(parsed_type.pointee_constant)
                        }),
                )?;
                self.variable_types
                    .insert(kernel_name.clone(), parsed_type.c_type);
                if let Some(struct_name) = &struct_pointer_name {
                    self.variable_structs
                        .insert(kernel_name, struct_name.clone());
                }
            }
            if self.peek() != Some(&Token::Comma) {
                break;
            }
            self.position += 1;
            if is_extern && self.peek() == Some(&Token::Equal) {
                return Err(
                    self.error_here("`extern` global declarations may not have an initializer")
                );
            }
        }
        self.expect(Token::Semicolon)
    }

    pub(super) fn parse_inferred_global_array_initializer(
        &mut self,
        name: &str,
        element_type: C0Type,
    ) -> Result<Vec<C0Expression>, C0SyntaxError> {
        self.expect(Token::LBrace)?;
        let mut values = Vec::new();
        if self.peek() != Some(&Token::RBrace) {
            loop {
                if self.peek() == Some(&Token::LBracket) {
                    return Err(self.error_here(format!(
                        "inferred file-scope scalar array `{name}` requires positional initializers"
                    )));
                }
                let value = self.parse_expression()?;
                values.push(normalize_static_initializer(
                    self,
                    element_type,
                    false,
                    &value,
                    "global",
                    false,
                )?);
                match self.peek() {
                    Some(Token::Comma) => {
                        self.position += 1;
                        if self.peek() == Some(&Token::RBrace) {
                            break;
                        }
                    }
                    Some(Token::RBrace) => break,
                    Some(token) => {
                        return Err(self.error_here(format!(
                            "expected `,` or `}}` in inferred file-scope scalar array `{name}` initializer, got {}",
                            token.describe()
                        )));
                    }
                    None => {
                        return Err(self.error_here(format!(
                            "expected `,` or `}}` in inferred file-scope scalar array `{name}` initializer, got end of input"
                        )));
                    }
                }
            }
        }
        self.expect(Token::RBrace)?;
        Ok(values)
    }

    pub(super) fn parse_inferred_multidimensional_global_array_initializer(
        &mut self,
        name: &str,
        element_type: C0Type,
        inner_shape: &[u32],
    ) -> Result<(Vec<u32>, C0ArrayInitializer), C0SyntaxError> {
        self.expect(Token::LBrace)?;
        let mut values = Vec::new();
        let mut next = 0u32;
        let mut outer_length = 0u32;
        if self.peek() == Some(&Token::RBrace) {
            self.position += 1;
            return Err(self.error_here(format!(
                "inferred file-scope multidimensional array `{name}` requires a non-empty initializer"
            )));
        }
        loop {
            if self.peek() != Some(&Token::LBrace) {
                return Err(self.error_here(format!(
                    "nested initializer for inferred file-scope multidimensional array `{name}` expects `{}` groups",
                    inner_shape.len()
                )));
            }
            self.parse_sparse_array_initializer_level(
                name,
                inner_shape,
                0,
                &mut values,
                &mut next,
            )?;
            outer_length = outer_length.checked_add(1).ok_or_else(|| {
                self.error_here(format!(
                    "inferred file-scope multidimensional array `{name}` has too many initializer rows"
                ))
            })?;
            match self.peek() {
                Some(Token::Comma) => {
                    self.position += 1;
                    if self.peek() == Some(&Token::RBrace) {
                        break;
                    }
                }
                Some(Token::RBrace) => break,
                Some(token) => {
                    return Err(self.error_here(format!(
                        "expected `,` or `}}` in inferred file-scope multidimensional array `{name}` initializer, got {}",
                        token.describe()
                    )));
                }
                None => {
                    return Err(self.error_here(format!(
                        "expected `,` or `}}` in inferred file-scope multidimensional array `{name}` initializer, got end of input"
                    )));
                }
            }
        }
        self.expect(Token::RBrace)?;
        let mut shape = Vec::with_capacity(inner_shape.len() + 1);
        shape.push(outer_length);
        shape.extend_from_slice(inner_shape);
        let length = array_shape_element_count(&shape).ok_or_else(|| {
            self.error_here(format!(
                "inferred file-scope multidimensional array `{name}` dimensions are too large"
            ))
        })?;
        let initializer =
            self.normalized_array_initializer(element_type, length, values, "global", false)?;
        Ok((shape, initializer))
    }

    pub(super) fn parse_global_array_length(
        &mut self,
        name: &str,
    ) -> Result<Option<GlobalArrayLength>, C0SyntaxError> {
        if self.peek() != Some(&Token::LBracket) {
            return Ok(None);
        }
        self.position += 1;
        if self.peek() == Some(&Token::RBracket) {
            self.position += 1;
            let mut incomplete_shape = Vec::new();
            while self.peek() == Some(&Token::LBracket) {
                self.position += 1;
                let length = match self.peek().cloned() {
                    Some(Token::Number(number)) => {
                        self.position += 1;
                        let length =
                            parse_integer_literal_magnitude(&number).map_err(|reason| {
                                self.error_at_previous(format!(
                                    "invalid file-scope array length `{number}`: {reason}"
                                ))
                            })?;
                        u32::try_from(length).map_err(|_| {
                            self.error_at_previous(format!(
                                "file-scope array length `{number}` is out of range"
                            ))
                        })?
                    }
                    Some(token) => {
                        return Err(self.error_at_previous(format!(
                            "expected positive file-scope array length, got {}",
                            token.describe()
                        )));
                    }
                    None => {
                        return Err(self.error_here(
                            "expected positive file-scope array length, got end of input",
                        ));
                    }
                };
                if length == 0 {
                    return Err(self.error_at_previous(format!(
                        "file-scope array `{name}` must have positive length"
                    )));
                }
                incomplete_shape.push(length);
                self.expect(Token::RBracket)?;
            }
            return Ok(Some(GlobalArrayLength::Incomplete(incomplete_shape)));
        }
        let mut dimensions = Vec::new();
        loop {
            let length = match self.peek().cloned() {
                Some(Token::Number(number)) => {
                    self.position += 1;
                    let length = parse_integer_literal_magnitude(&number).map_err(|reason| {
                        self.error_at_previous(format!(
                            "invalid file-scope array length `{number}`: {reason}"
                        ))
                    })?;
                    u32::try_from(length).map_err(|_| {
                        self.error_at_previous(format!(
                            "file-scope array length `{number}` is out of range"
                        ))
                    })?
                }
                Some(token) => {
                    return Err(self.error_at_previous(format!(
                        "expected positive file-scope array length, got {}",
                        token.describe()
                    )));
                }
                None => {
                    return Err(self.error_here(
                        "expected positive file-scope array length, got end of input",
                    ));
                }
            };
            if length == 0 {
                return Err(self.error_at_previous(format!(
                    "file-scope array `{name}` must have positive length"
                )));
            }
            dimensions.push(length);
            self.expect(Token::RBracket)?;
            if self.peek() != Some(&Token::LBracket) {
                break;
            }
            self.position += 1;
        }
        Ok(Some(GlobalArrayLength::Complete(dimensions)))
    }

    pub(super) fn parse_global_array_initializer(
        &mut self,
        name: &str,
        element_type: C0Type,
        shape: &[u32],
    ) -> Result<C0ArrayInitializer, C0SyntaxError> {
        let length = array_shape_element_count(shape).expect("validated global array shape");
        if shape.len() == 1 {
            self.parse_scalar_array_initializer(name, element_type, length, false)
        } else {
            let mut values = Vec::new();
            let mut next = 0u32;
            self.parse_sparse_array_initializer_level(name, shape, 0, &mut values, &mut next)?;
            self.normalized_array_initializer(element_type, length, values, "global", false)
        }
    }

    /// The initializer of `length` elements of `element_type` whose written
    /// elements are `values`, ascending by index, each normalized as a
    /// static initializer of `storage`.
    pub(super) fn normalized_array_initializer(
        &self,
        element_type: C0Type,
        length: u32,
        values: Vec<(u32, C0Expression)>,
        storage: &str,
        static_local: bool,
    ) -> Result<C0ArrayInitializer, C0SyntaxError> {
        let values = values
            .into_iter()
            .map(|(index, value)| {
                normalize_static_initializer(
                    self,
                    element_type,
                    false,
                    &value,
                    storage,
                    static_local,
                )
                .map(|value| (index, value))
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(C0ArrayInitializer::new(length, element_type, values))
    }

    pub(super) fn parse_scalar_array_initializer(
        &mut self,
        name: &str,
        element_type: C0Type,
        length: u32,
        static_local: bool,
    ) -> Result<C0ArrayInitializer, C0SyntaxError> {
        let context = if static_local {
            "static local scalar array"
        } else {
            "file-scope scalar array"
        };
        self.expect(Token::LBrace)?;
        let mut values = BTreeMap::new();
        let mut next_element_index = 0u32;
        if self.peek() != Some(&Token::RBrace) {
            loop {
                let element_index = if self.peek() == Some(&Token::LBracket) {
                    self.position += 1;
                    let index = self.parse_scalar_array_designator(name, length, context)?;
                    self.expect(Token::Equal)?;
                    next_element_index = index
                        .checked_add(1)
                        .expect("validated scalar array designator index");
                    index
                } else {
                    if next_element_index >= length {
                        return Err(self.error_here(format!(
                            "too many initializers for {context} `{name}[{length}]`"
                        )));
                    }
                    let index = next_element_index;
                    next_element_index = next_element_index
                        .checked_add(1)
                        .expect("validated scalar array initializer index");
                    index
                };
                if values.contains_key(&element_index) {
                    return Err(self.error_here(format!(
                        "duplicate designator for {context} `{name}[{element_index}]`"
                    )));
                }
                let value = self.parse_expression()?;
                let value = if static_local {
                    normalize_static_initializer(
                        self,
                        element_type,
                        false,
                        &value,
                        "static local",
                        true,
                    )?
                } else {
                    normalize_static_initializer(
                        self,
                        element_type,
                        false,
                        &value,
                        "global",
                        false,
                    )?
                };
                values.insert(element_index, value);
                match self.peek() {
                    Some(Token::Comma) => {
                        self.position += 1;
                        if self.peek() == Some(&Token::RBrace) {
                            break;
                        }
                    }
                    Some(Token::RBrace) => break,
                    Some(token) => {
                        return Err(self.error_here(format!(
                            "expected `,` or `}}` in {context} `{name}` initializer, got {}",
                            token.describe()
                        )));
                    }
                    None => {
                        return Err(self.error_here(format!(
                            "expected `,` or `}}` in {context} `{name}` initializer, got end of input"
                        )));
                    }
                }
            }
        }
        self.expect(Token::RBrace)?;
        Ok(C0ArrayInitializer::new(length, element_type, values))
    }

    pub(super) fn parse_scalar_array_designator(
        &mut self,
        name: &str,
        length: u32,
        context: &str,
    ) -> Result<u32, C0SyntaxError> {
        let index = match self.next() {
            Some(Token::Number(number)) => {
                let magnitude = parse_integer_literal_magnitude(&number).map_err(|reason| {
                    self.error_at_previous(format!(
                        "invalid {context} designator index `{number}`: {reason}"
                    ))
                })?;
                u32::try_from(magnitude).map_err(|_| {
                    self.error_at_previous(format!(
                        "{context} designator index `{number}` is out of range"
                    ))
                })?
            }
            Some(Token::CharLiteral(value)) => self.character_designator_index(value)?,
            Some(token) => {
                return Err(self.error_at_previous(format!(
                    "{context} designators currently require integer literals, got {}",
                    token.describe()
                )));
            }
            None => {
                return Err(self.error_here(format!(
                    "{context} designators currently require an integer literal"
                )));
            }
        };
        self.expect(Token::RBracket)?;
        if index >= length {
            return Err(self.error_here(format!(
                "{context} designator index `{index}` is out of bounds for `{name}[{length}]`"
            )));
        }
        Ok(index)
    }

    pub(super) fn register_global_declaration(
        &mut self,
        name: String,
        c_type: C0Type,
        declaration: C0Global,
    ) -> Result<(), C0SyntaxError> {
        if self.function_declarations.contains_key(&name)
            || self.global_arrays.contains_key(&name)
            || self.global_aggregates.contains_key(&name)
            || self.global_aggregate_arrays.contains_key(&name)
        {
            return Err(self.error_here(format!(
                "global `{name}` conflicts with a function or array declaration"
            )));
        }
        if let Some(previous) = self.globals.get(&name) {
            if previous.c_type != c_type || previous.struct_name != declaration.struct_name {
                return Err(
                    self.error_here(format!("conflicting declarations for global `{name}`"))
                );
            }
            if previous.is_volatile() != declaration.is_volatile() {
                return Err(self.error_here(format!(
                    "conflicting volatile qualifiers for global `{name}`"
                )));
            }
            if previous.is_constant() != declaration.is_constant() {
                return Err(
                    self.error_here(format!("conflicting const qualifiers for global `{name}`"))
                );
            }
            if previous.pointee_is_constant() != declaration.pointee_is_constant() {
                return Err(self.error_here(format!(
                    "conflicting pointee const qualifiers for global `{name}`"
                )));
            }
            if previous.is_file_static() != declaration.is_file_static() {
                return Err(self.error_here(format!(
                    "conflicting linkage declarations for global `{name}`"
                )));
            }
            if previous.is_initialized_definition() && declaration.is_initialized_definition() {
                return Err(self.error_here(format!("duplicate definition of global `{name}`")));
            }
        }
        let merged = match self.globals.get(&name) {
            Some(previous) if previous.is_initialized_definition() => previous.clone(),
            Some(_) if declaration.is_initialized_definition() => declaration,
            Some(previous) if previous.is_tentative() => previous.clone(),
            _ => declaration,
        };
        self.globals.insert(name, merged);
        Ok(())
    }

    pub(super) fn register_global_array_declaration(
        &mut self,
        name: String,
        element_type: C0Type,
        declaration: C0GlobalArray,
    ) -> Result<(), C0SyntaxError> {
        if self.function_declarations.contains_key(&name)
            || self.globals.contains_key(&name)
            || self.global_aggregates.contains_key(&name)
            || self.global_aggregate_arrays.contains_key(&name)
        {
            return Err(self.error_here(format!(
                "global `{name}` conflicts with a function or scalar global declaration"
            )));
        }
        if let Some(previous) = self.global_arrays.get(&name) {
            if previous.element_type != element_type
                || !array_shapes_compatible(previous, &declaration)
            {
                return Err(self.error_here(format!(
                    "conflicting declarations for global array `{name}`"
                )));
            }
            if previous.is_constant() != declaration.is_constant() {
                return Err(self.error_here(format!(
                    "conflicting const qualifiers for global array `{name}`"
                )));
            }
            if previous.is_file_static() != declaration.is_file_static() {
                return Err(self.error_here(format!(
                    "conflicting linkage declarations for global array `{name}`"
                )));
            }
            if previous.is_initialized_definition() && declaration.is_initialized_definition() {
                return Err(
                    self.error_here(format!("duplicate definition of global array `{name}`"))
                );
            }
        }
        let merged = merge_global_array_declarations(self.global_arrays.get(&name), declaration);
        self.global_arrays.insert(name, merged);
        Ok(())
    }

    pub(super) fn register_global_aggregate_declaration(
        &mut self,
        name: String,
        declaration: C0GlobalAggregate,
    ) -> Result<(), C0SyntaxError> {
        if self.function_declarations.contains_key(&name)
            || self.globals.contains_key(&name)
            || self.global_arrays.contains_key(&name)
            || self.global_aggregate_arrays.contains_key(&name)
        {
            return Err(self.error_here(format!(
                "global `{name}` conflicts with a function or scalar declaration"
            )));
        }
        if let Some(previous) = self.global_aggregates.get(&name) {
            if previous.struct_name() != declaration.struct_name()
                || previous.layout() != declaration.layout()
            {
                return Err(self.error_here(format!(
                    "conflicting declarations for aggregate global `{name}`"
                )));
            }
            if previous.is_constant() != declaration.is_constant() {
                return Err(self.error_here(format!(
                    "conflicting const qualifiers for aggregate global `{name}`"
                )));
            }
            if previous.is_file_static() != declaration.is_file_static() {
                return Err(self.error_here(format!(
                    "conflicting linkage declarations for aggregate global `{name}`"
                )));
            }
            if previous.is_initialized_definition() && declaration.is_initialized_definition() {
                return Err(
                    self.error_here(format!("duplicate definition of aggregate global `{name}`"))
                );
            }
        }
        let merged = match self.global_aggregates.get(&name) {
            Some(previous) if previous.is_initialized_definition() => previous.clone(),
            Some(_) if declaration.is_initialized_definition() => declaration,
            Some(previous) if previous.is_tentative() => previous.clone(),
            _ => declaration,
        };
        self.global_aggregates.insert(name, merged);
        Ok(())
    }

    pub(super) fn register_global_aggregate_array_declaration(
        &mut self,
        name: String,
        declaration: C0GlobalAggregateArray,
    ) -> Result<(), C0SyntaxError> {
        if self.function_declarations.contains_key(&name)
            || self.globals.contains_key(&name)
            || self.global_arrays.contains_key(&name)
            || self.global_aggregates.contains_key(&name)
        {
            return Err(self.error_here(format!(
                "global `{name}` conflicts with a function or non-array declaration"
            )));
        }
        if let Some(previous) = self.global_aggregate_arrays.get(&name) {
            if previous.struct_name() != declaration.struct_name()
                || previous.layout() != declaration.layout()
                || !array_lengths_compatible(previous.array_length(), declaration.array_length())
            {
                return Err(self.error_here(format!(
                    "conflicting declarations for aggregate global array `{name}`"
                )));
            }
            if previous.is_constant() != declaration.is_constant() {
                return Err(self.error_here(format!(
                    "conflicting const qualifiers for aggregate global array `{name}`"
                )));
            }
            if previous.is_file_static() != declaration.is_file_static() {
                return Err(self.error_here(format!(
                    "conflicting linkage declarations for aggregate global array `{name}`"
                )));
            }
            if previous.is_initialized_definition() && declaration.is_initialized_definition() {
                return Err(self.error_here(format!(
                    "duplicate definition of aggregate global array `{name}`"
                )));
            }
        }
        let merged = match self.global_aggregate_arrays.get(&name) {
            Some(previous) if previous.is_initialized_definition() => previous.clone(),
            Some(_) if declaration.is_initialized_definition() => declaration,
            Some(previous) if previous.is_tentative() => previous.clone(),
            _ => declaration,
        };
        self.global_aggregate_arrays.insert(name, merged);
        Ok(())
    }
}
