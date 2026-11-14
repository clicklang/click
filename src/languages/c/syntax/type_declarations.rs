//! Parsing typedef, enum, union and struct declarations and struct field declarators.

use super::*;

impl Parser {
    pub(super) fn parse_typedef_declaration(&mut self) -> Result<(), C0SyntaxError> {
        self.expect_ident_spelling("typedef")?;
        let mut parsed_type = self.parse_type_with_anonymous_struct(true, true, true)?;
        let alias = if let Some((alias, interface_type, signature)) =
            self.parse_function_pointer_declarator(parsed_type.clone())?
        {
            // The callback's return qualifiers and nominal tags belong to its
            // signature, not to the function-pointer object named by this alias.
            parsed_type.interface_type = interface_type;
            parsed_type.function_pointer_signature = Some(signature);
            parsed_type.struct_name = None;
            parsed_type.enum_name = None;
            parsed_type.union_name = None;
            parsed_type.is_constant = false;
            parsed_type.pointee_constant = false;
            parsed_type.is_volatile = false;
            parsed_type.volatile_levels = 0;
            parsed_type.pointer_depth = 0;
            alias
        } else {
            self.expect_ident("typedef name")?
        };
        if self.peek() == Some(&Token::LBracket) {
            self.position += 1;
            let length = self.parse_struct_array_length()?;
            self.expect(Token::RBracket)?;
            if self.peek() == Some(&Token::LBracket) {
                return Err(
                    self.error_here("multidimensional typedef arrays are not supported yet")
                );
            }
            if parsed_type.struct_name.is_some() || parsed_type.union_name.is_some() {
                return Err(self.error_here("aggregate typedef arrays are not supported yet"));
            }
            parsed_type.compatibility_identity = CompatibilityIdentity::Unavailable;
            parsed_type.interface_type = array_type_for_element(parsed_type.interface_type, length)
                .ok_or_else(|| self.error_here("typedef array element type is unsupported"))?;
        }
        if self.peek_ident() == Some("__attribute__") {
            self.position += 1;
            self.expect(Token::LParen)?;
            self.expect(Token::LParen)?;
            let attribute = self.expect_ident("GNU typedef attribute")?;
            match attribute.as_str() {
                "aligned" | "__aligned__" => {
                    // The argument-free spelling requests the target's maximum
                    // useful alignment. Do not guess its host ABI value.
                    parsed_type.aligned_typedef = true;
                }
                "mode" | "__mode__" => {
                    self.expect(Token::LParen)?;
                    let mode = self.expect_ident("GNU integer mode")?;
                    if mode != "word" && mode != "__word__" {
                        return Err(self
                            .error_at_previous(format!("unsupported GNU integer mode `{mode}`")));
                    }
                    self.expect(Token::RParen)?;
                    if parsed_type.enum_name.is_some()
                        || parsed_type.struct_name.is_some()
                        || parsed_type.union_name.is_some()
                    {
                        return Err(self.error_at_previous(
                            "GNU word mode requires an ordinary integer typedef",
                        ));
                    }
                    parsed_type.compatibility_identity = CompatibilityIdentity::Unavailable;
                    // Both supported x86-64 targets have a 64-bit machine word.
                    // This changes width, not signedness or object qualifiers.
                    parsed_type.interface_type = match parsed_type.interface_type {
                        InterfaceType::Int8
                        | InterfaceType::Int16
                        | InterfaceType::Int32
                        | InterfaceType::Int64(_)
                        | InterfaceType::Int128 => InterfaceType::Int64(LongRank::Long),
                        InterfaceType::UInt8
                        | InterfaceType::UInt16
                        | InterfaceType::UInt32
                        | InterfaceType::UInt64(_)
                        | InterfaceType::UInt128 => InterfaceType::UInt64(LongRank::Long),
                        _ => {
                            return Err(self.error_at_previous(
                                "GNU word mode requires an ordinary integer typedef",
                            ));
                        }
                    };
                }
                _ => {
                    return Err(self.error_at_previous(format!(
                        "unsupported GNU typedef attribute `{attribute}`"
                    )));
                }
            }
            self.expect(Token::RParen)?;
            self.expect(Token::RParen)?;
        }
        self.expect(Token::Semicolon)?;
        if self.typedefs.insert(alias.clone(), parsed_type).is_some() {
            return Err(self.error_at_previous(format!("duplicate typedef `{alias}`")));
        }
        Ok(())
    }

    pub(super) fn parse_enum_declaration(&mut self) -> Result<(), C0SyntaxError> {
        self.parse_enum_specifier_body()?;
        self.expect(Token::Semicolon)?;
        Ok(())
    }

    /// Parses `enum [tag] { enumerators }` and records the enumeration,
    /// returning its name: the tag, or a fresh name for an anonymous one.
    pub(super) fn parse_enum_specifier_body(&mut self) -> Result<String, C0SyntaxError> {
        self.expect_ident_spelling("enum")?;
        let name = if self.peek() == Some(&Token::LBrace) {
            format!(
                "#anonymous-enum:{}:{}",
                self.source_identity.as_deref().unwrap_or("source"),
                self.position
            )
        } else {
            self.expect_ident("enum name")?
        };
        if self.enums.contains_key(&name) {
            return Err(self.error_at_previous(format!("duplicate enum declaration `{name}`")));
        }
        self.expect(Token::LBrace)?;
        if self.peek() == Some(&Token::RBrace) {
            return Err(self.error_here("enum declarations must contain at least one enumerator"));
        }

        let mut values = BTreeMap::new();
        let mut next_value = 0i64;
        loop {
            let enumerator = self.expect_ident("enumerator name")?;
            if self.enum_constants.contains_key(&enumerator) {
                return Err(self.error_at_previous(format!("duplicate enumerator `{enumerator}`")));
            }
            let value = if self.peek() == Some(&Token::Equal) {
                self.position += 1;
                self.parse_enum_value(&name)?
            } else {
                next_value
            };
            // Until the enumeration is complete, a constant that fits `int`
            // has type `int` (C23 6.7.2.2p11).
            let provisional = enum_constant_literal(value, InterfaceType::Int32)
                .or_else(|| enum_constant_literal(value, InterfaceType::UInt32))
                .ok_or_else(|| {
                    self.error_here(format!(
                        "enum `{name}` value {value} needs a type wider than 32 bits"
                    ))
                })?;
            values.insert(enumerator.clone(), value);
            self.enum_constants.insert(enumerator, provisional);
            next_value = value
                .checked_add(1)
                .ok_or_else(|| self.error_here(format!("enum `{name}` value is too large")))?;

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
                        "expected `,` or `}}` in enum `{name}`, got {}",
                        token.describe()
                    )));
                }
                None => {
                    return Err(self.error_here(format!(
                        "expected `,` or `}}` in enum `{name}`, got end of input"
                    )));
                }
            }
        }
        self.expect(Token::RBrace)?;

        // GCC and Clang give an enumeration with no negative value the
        // compatible type `unsigned int`, and one with a negative value
        // `int`; a range neither holds needs a wider type, which Click does
        // not model.
        let negative = values.values().any(|value| *value < 0);
        let compatible_type = if negative {
            InterfaceType::Int32
        } else {
            InterfaceType::UInt32
        };
        if values
            .values()
            .any(|value| enum_constant_literal(*value, compatible_type).is_none())
        {
            return Err(self.error_here(format!(
                "enum `{name}` values need a type wider than 32 bits"
            )));
        }
        // After completion, the constants are `int` when every value fits
        // `int`, and otherwise have the enumerated type (C23 6.7.2.2p15),
        // as GCC 13 types them; Clang 18 keeps the fitting ones `int`.
        let constant_type = if values.values().all(|value| i32::try_from(*value).is_ok()) {
            InterfaceType::Int32
        } else {
            compatible_type
        };
        for (enumerator, value) in &values {
            let literal = enum_constant_literal(*value, constant_type)
                .expect("validated enumerator fits its constant type");
            self.enum_constants.insert(enumerator.clone(), literal);
        }
        self.enums.insert(
            name.clone(),
            C0EnumDefinition {
                values,
                compatible_type,
            },
        );
        Ok(name)
    }

    pub(super) fn parse_enum_value(&mut self, enum_name: &str) -> Result<i64, C0SyntaxError> {
        let expression = self.parse_expression()?;
        let value = evaluate_static_integer_expression(&expression).map_err(|_| {
            self.error_here(format!(
                "enum `{enum_name}` value must be an integer constant expression"
            ))
        })?;
        match value {
            StaticIntegerValue::Signed { value, .. } => i64::try_from(value),
            StaticIntegerValue::Unsigned { value, .. } => i64::try_from(value),
        }
        .map_err(|_| {
            self.error_here(format!(
                "enum `{enum_name}` value needs a type wider than 32 bits"
            ))
        })
    }

    pub(super) fn parse_union_declaration(&mut self) -> Result<(), C0SyntaxError> {
        self.expect_ident_spelling("union")?;
        let name = self.expect_ident("union name")?;
        self.parse_union_body(name)?;
        self.expect(Token::Semicolon)
    }

    // Named declarations and anonymous typedefs share the same ABI layout.
    // The caller consumes the declarator and its trailing semicolon.
    pub(super) fn parse_union_body(&mut self, name: String) -> Result<(), C0SyntaxError> {
        if self.unions.contains_key(&name) {
            return Err(self.error_at_previous(format!("duplicate union declaration `{name}`")));
        }
        self.expect(Token::LBrace)?;

        let mut fields = BTreeMap::new();
        let mut union_size = 0u32;
        let mut union_alignment = 1u32;
        while self.peek() != Some(&Token::RBrace) {
            if self.peek().is_none() {
                return Err(self.error_here("expected union field or `}`, got end of input"));
            }
            if self.peek_ident() == Some("_Static_assert") {
                self.parse_static_assert()?;
                continue;
            }
            // GNU __extension__ suppresses a compiler diagnostic for the
            // following declaration without changing its type or layout.
            if self.peek_ident() == Some("__extension__") {
                self.position += 1;
            }
            let field_type = self.parse_type_with_anonymous_struct(true, true, false)?;
            if field_type.function_pointer_signature.is_some() {
                return Err(
                    self.error_here("union callback fields need nominal signature metadata")
                );
            }
            loop {
                let field_name = self.expect_ident("union field name")?;
                let (
                    interface_type,
                    field_size,
                    mut field_alignment,
                    field_struct_name,
                    array_element_width,
                    array_shape,
                ) = self.parse_struct_field_declarator(&field_type, &name)?;
                if let Some(attribute_alignment) = self.consume_field_alignment_attribute()? {
                    field_alignment = field_alignment.max(attribute_alignment);
                }
                if fields
                    .insert(
                        field_name.clone(),
                        C0UnionField {
                            interface_type,
                            long_double: field_type.long_double,
                            pointee_constant: field_type.pointee_constant,
                            enum_name: (interface_type == field_type.interface_type)
                                .then(|| field_type.enum_name.clone())
                                .flatten(),
                            struct_name: field_struct_name,
                            union_name: (interface_type == field_type.interface_type)
                                .then(|| field_type.union_name.clone())
                                .flatten(),
                            array_element_width,
                            array_shape,
                            offset_bytes: 0,
                            byte_width: field_size,
                        },
                    )
                    .is_some()
                {
                    return Err(self
                        .error_here(format!("duplicate field `{field_name}` in union `{name}`")));
                }
                union_size = union_size.max(field_size);
                union_alignment = union_alignment.max(field_alignment);
                if self.peek() != Some(&Token::Comma) {
                    break;
                }
                self.position += 1;
            }
            self.expect(Token::Semicolon)?;
        }

        self.expect(Token::RBrace)?;
        if fields.is_empty() {
            return Err(self.error_here("union declarations must contain at least one field"));
        }
        let size_bytes = align_up(union_size, union_alignment)
            .ok_or_else(|| self.error_here(format!("union `{name}` layout is too large")))?;
        self.unions.insert(
            name,
            C0UnionLayout {
                fields,
                size_bytes,
                alignment_bytes: union_alignment,
            },
        );
        Ok(())
    }

    pub(super) fn parse_struct_declaration(&mut self) -> Result<(), C0SyntaxError> {
        self.expect_ident_spelling("struct")?;
        let name = self.expect_ident("struct name")?;
        self.parse_struct_body(name)?;
        self.expect(Token::Semicolon)
    }

    // Both named declarations and anonymous typedefs use the same layout and
    // field validation. The caller owns the following declarator/semicolon.
    pub(super) fn parse_struct_body(&mut self, name: String) -> Result<(), C0SyntaxError> {
        self.expect(Token::LBrace)?;

        let mut fields = BTreeMap::new();
        let mut offset_bytes = 0u32;
        let mut struct_alignment = 1u32;
        while self.peek() != Some(&Token::RBrace) {
            if self.peek().is_none() {
                return Err(self.error_here("expected struct field or `}`, got end of input"));
            }
            if self.peek_ident() == Some("_Static_assert") {
                self.parse_static_assert()?;
                continue;
            }
            let field_type = self.parse_type_with_anonymous_struct(false, true, false)?;
            if let Some((field_name, interface_type, function_pointer_signature)) =
                self.parse_function_pointer_declarator(field_type.clone())?
            {
                let (field_size, mut field_alignment) = self.abi.size_and_alignment(interface_type);
                if let Some(attribute_alignment) = self.consume_field_alignment_attribute()? {
                    field_alignment = field_alignment.max(attribute_alignment);
                }
                offset_bytes = align_up(offset_bytes, field_alignment).ok_or_else(|| {
                    self.error_here(format!("struct `{name}` layout is too large"))
                })?;
                if fields
                    .insert(
                        field_name.clone(),
                        RecordField {
                            interface_type,
                            long_double: false,
                            pointee_constant: false,
                            struct_name: None,
                            enum_name: None,
                            union_name: None,
                            function_pointer_signature: Some(function_pointer_signature),
                            array_element_width: None,
                            array_shape: None,
                            offset_bytes,
                            byte_width: field_size,
                        },
                    )
                    .is_some()
                {
                    return Err(self
                        .error_here(format!("duplicate field `{field_name}` in struct `{name}`")));
                }
                offset_bytes = offset_bytes.checked_add(field_size).ok_or_else(|| {
                    self.error_here(format!("struct `{name}` layout is too large"))
                })?;
                struct_alignment = struct_alignment.max(field_alignment);
                self.expect(Token::Semicolon)?;
                continue;
            }
            loop {
                let field_name = self.expect_ident("struct field name")?;
                let (
                    interface_type,
                    field_size,
                    mut field_alignment,
                    field_struct_name,
                    array_element_width,
                    array_shape,
                ) = self.parse_struct_field_declarator(&field_type, &name)?;
                if let Some(attribute_alignment) = self.consume_field_alignment_attribute()? {
                    field_alignment = field_alignment.max(attribute_alignment);
                }
                offset_bytes = align_up(offset_bytes, field_alignment).ok_or_else(|| {
                    self.error_here(format!("struct `{name}` layout is too large"))
                })?;
                if fields
                    .insert(
                        field_name.clone(),
                        RecordField {
                            interface_type,
                            long_double: field_type.long_double,
                            pointee_constant: field_type.pointee_constant,
                            struct_name: field_struct_name,
                            enum_name: (interface_type == field_type.interface_type)
                                .then(|| field_type.enum_name.clone())
                                .flatten(),
                            union_name: (interface_type == field_type.interface_type)
                                .then(|| field_type.union_name.clone())
                                .flatten(),
                            function_pointer_signature: field_type
                                .function_pointer_signature
                                .clone(),
                            array_element_width,
                            array_shape,
                            offset_bytes,
                            byte_width: field_size,
                        },
                    )
                    .is_some()
                {
                    return Err(self
                        .error_here(format!("duplicate field `{field_name}` in struct `{name}`")));
                }
                offset_bytes = offset_bytes.checked_add(field_size).ok_or_else(|| {
                    self.error_here(format!("struct `{name}` layout is too large"))
                })?;
                struct_alignment = struct_alignment.max(field_alignment);
                if self.peek() != Some(&Token::Comma) {
                    break;
                }
                self.position += 1;
            }
            self.expect(Token::Semicolon)?;
        }

        self.expect(Token::RBrace)?;
        if let Some(attribute_alignment) = self.consume_struct_alignment_attribute()? {
            struct_alignment = struct_alignment.max(attribute_alignment);
        }

        if fields.is_empty() {
            return Err(self.error_here("struct declarations must contain at least one field"));
        }
        let size_bytes = align_up(offset_bytes, struct_alignment)
            .ok_or_else(|| self.error_here(format!("struct `{name}` layout is too large")))?;
        let (aggregate_fields, aggregate_unions) =
            flatten_aggregate_layout(&fields, &self.structs, &self.unions);
        let class = struct_class_of_fields(&name, &fields, &self.structs, &self.unions);
        if self
            .structs
            .insert(
                name.clone(),
                RecordLayout {
                    fields,
                    aggregate_fields,
                    aggregate_unions,
                    size_bytes,
                    alignment_bytes: struct_alignment,
                    class: Some(class),
                },
            )
            .is_some()
        {
            return Err(self.error_here(format!("duplicate struct declaration `{name}`")));
        }

        Ok(())
    }

    pub(super) fn parse_struct_field_declarator(
        &mut self,
        base_type: &ParsedType,
        struct_name: &str,
    ) -> Result<
        (
            InterfaceType,
            u32,
            u32,
            Option<String>,
            Option<u32>,
            Option<Vec<u32>>,
        ),
        C0SyntaxError,
    > {
        if base_type.long_double {
            if base_type.is_volatile || base_type.is_constant {
                return Err(
                    self.error_here("qualified long double fields need a typed value model")
                );
            }
            if self.peek() == Some(&Token::LBracket) {
                return Err(
                    self.error_here("arrays of long double values need a typed value model")
                );
            }
            return Ok((InterfaceType::UInt8Array(16), 16, 16, None, None, None));
        }
        if base_type.is_volatile {
            return Err(self.error_here(
                "the small volatile model does not support volatile struct or union fields",
            ));
        }
        if base_type.is_constant {
            return Err(self.error_here(
                "const-qualified struct or union fields are not supported in this slice",
            ));
        }
        if let Some(enum_name) = base_type.enum_name.as_deref() {
            if !self.enums.contains_key(enum_name) {
                return Err(self.error_here(format!("unknown enum declaration `{enum_name}`")));
            }
            if base_type.interface_type.is_pointer() {
                return Err(self.error_here("pointers to enum values are not supported"));
            }
            if self.peek() == Some(&Token::LBracket) {
                return Err(self.error_here("arrays of enum fields are not supported"));
            }
            return Ok((base_type.interface_type, 4, 4, None, None, None));
        }
        if let Some(union_name) = base_type.union_name.as_deref() {
            let union_layout = self.unions.get(union_name).ok_or_else(|| {
                self.error_here(format!("unknown embedded union declaration `{union_name}`"))
            })?;
            if self.peek() == Some(&Token::LBracket) {
                return Err(
                    self.error_here("arrays of embedded unions are not supported in struct fields")
                );
            }
            return Ok((
                base_type.interface_type,
                union_layout.size_bytes(),
                union_layout.alignment_bytes(),
                None,
                None,
                None,
            ));
        }
        if is_plain_struct_type(base_type) {
            let nested_name = base_type
                .struct_name
                .as_deref()
                .expect("plain struct type carries its name");
            let nested_layout = self.structs.get(nested_name).cloned().ok_or_else(|| {
                self.error_here(format!(
                    "unknown embedded struct declaration `{nested_name}`"
                ))
            })?;
            if self.peek() == Some(&Token::LBracket) {
                let mut dimensions = Vec::new();
                while self.peek() == Some(&Token::LBracket) {
                    self.position += 1;
                    let length = self.parse_struct_array_length()?;
                    self.expect(Token::RBracket)?;
                    dimensions.push(length);
                }
                let element_count = dimensions.iter().try_fold(1u32, |count, length| {
                    count.checked_mul(*length).ok_or_else(|| {
                        self.error_here(format!("struct `{struct_name}` layout is too large"))
                    })
                })?;
                let field_size = nested_layout
                    .size_bytes
                    .checked_mul(element_count)
                    .ok_or_else(|| {
                        self.error_here(format!("struct `{struct_name}` layout is too large"))
                    })?;
                return Ok((
                    InterfaceType::UInt8Array(field_size),
                    field_size,
                    nested_layout.alignment_bytes(),
                    Some(nested_name.to_string()),
                    Some(nested_layout.size_bytes()),
                    Some(dimensions),
                ));
            }
            return Ok((
                base_type.interface_type,
                nested_layout.size_bytes(),
                nested_layout.alignment_bytes(),
                Some(nested_name.to_string()),
                None,
                None,
            ));
        }
        let (interface_type, array_shape) = if self.peek() == Some(&Token::LBracket) {
            if (base_type.struct_name.is_some() && !base_type.interface_type.is_pointer())
                || !matches!(
                    base_type.interface_type,
                    InterfaceType::Int32
                        | InterfaceType::UInt32
                        | InterfaceType::Int64(_)
                        | InterfaceType::UInt64(_)
                        | InterfaceType::Char(_)
                        | InterfaceType::UInt8
                        | InterfaceType::Float32
                        | InterfaceType::Float64
                ) && pointer_array_element(base_type.interface_type).is_none()
            {
                return Err(self.error_here(
                    "inline scalar arrays in structs currently support int32, uint32, int64, uint64, uint8, float, and double elements",
                ));
            }
            let mut dimensions = Vec::new();
            let mut element_count = 1u32;
            while self.peek() == Some(&Token::LBracket) {
                self.position += 1;
                let length = self.parse_struct_array_length()?;
                element_count = element_count.checked_mul(length).ok_or_else(|| {
                    self.error_here(format!(
                        "struct array dimensions are too large for `{struct_name}`"
                    ))
                })?;
                dimensions.push(length);
                self.expect(Token::RBracket)?;
            }

            let array_shape = (dimensions.len() > 1).then_some(dimensions);
            let interface_type = match base_type.interface_type {
                InterfaceType::Int32 => InterfaceType::Int32Array(element_count),
                InterfaceType::UInt32 => InterfaceType::UInt32Array(element_count),
                InterfaceType::Int64(rank) => InterfaceType::Int64Array(rank, element_count),
                InterfaceType::Int128 => InterfaceType::Int128Array(element_count),
                InterfaceType::UInt64(rank) => InterfaceType::UInt64Array(rank, element_count),
                InterfaceType::UInt128 => InterfaceType::UInt128Array(element_count),
                InterfaceType::Char(plain) => InterfaceType::CharArray(plain, element_count),
                InterfaceType::UInt8 => InterfaceType::UInt8Array(element_count),
                InterfaceType::Float32 => InterfaceType::Float32Array(element_count),
                InterfaceType::Float64 => InterfaceType::Float64Array(element_count),
                pointer => InterfaceType::PointerArray(
                    pointer_array_element(pointer)
                        .expect("validated pointer struct array element type"),
                    pointer.long_rank().unwrap_or(LongRank::Long),
                    element_count,
                ),
            };
            (interface_type, array_shape)
        } else {
            (base_type.interface_type, None)
        };

        if !interface_type.is_pointer()
            && !matches!(
                interface_type,
                InterfaceType::Bool
                    | InterfaceType::Int8
                    | InterfaceType::Int16
                    | InterfaceType::Int32
                    | InterfaceType::Char(_)
                    | InterfaceType::UInt8
                    | InterfaceType::UInt16
                    | InterfaceType::UInt32
                    | InterfaceType::Int64(_)
                    | InterfaceType::UInt64(_)
                    | InterfaceType::Float32
                    | InterfaceType::Float64
                    | InterfaceType::Int32Pointer
                    | InterfaceType::CharPointer(_)
                    | InterfaceType::UInt8Pointer
                    | InterfaceType::Float32Pointer
                    | InterfaceType::Float64Pointer
                    | InterfaceType::Int32PointerPointer
                    | InterfaceType::CharPointerPointer(_)
                    | InterfaceType::UInt8PointerPointer
                    | InterfaceType::Float32PointerPointer
                    | InterfaceType::Float64PointerPointer
                    | InterfaceType::Int32Array(_)
                    | InterfaceType::UInt32Array(_)
                    | InterfaceType::Int128Array(_)
                    | InterfaceType::Int64Array(_, _)
                    | InterfaceType::UInt128Array(_)
                    | InterfaceType::UInt64Array(_, _)
                    | InterfaceType::CharArray(_, _)
                    | InterfaceType::UInt8Array(_)
                    | InterfaceType::Float32Array(_)
                    | InterfaceType::Float64Array(_)
                    | InterfaceType::PointerArray(_, _, _)
            )
        {
            return Err(self.error_here(format!(
                "struct `{struct_name}` fields currently support modeled scalars, fixed arrays, and pointer fields",
            )));
        }
        let (field_size, field_alignment) = match interface_type {
            InterfaceType::Int32Array(length) | InterfaceType::UInt32Array(length) => (
                length.checked_mul(4).ok_or_else(|| {
                    self.error_here(format!("struct `{struct_name}` layout is too large"))
                })?,
                4,
            ),
            InterfaceType::Int64Array(_, length) | InterfaceType::UInt64Array(_, length) => (
                length.checked_mul(8).ok_or_else(|| {
                    self.error_here(format!("struct `{struct_name}` layout is too large"))
                })?,
                8,
            ),
            InterfaceType::Int128Array(length) | InterfaceType::UInt128Array(length) => (
                length.checked_mul(16).ok_or_else(|| {
                    self.error_here(format!("struct `{struct_name}` layout is too large"))
                })?,
                16,
            ),
            InterfaceType::CharArray(_, length) => (length, 1),
            InterfaceType::UInt8Array(length) => (length, 1),
            InterfaceType::PointerArray(_, _, length) => (
                length.checked_mul(8).ok_or_else(|| {
                    self.error_here(format!("struct `{struct_name}` layout is too large"))
                })?,
                8,
            ),
            _ => self.abi.size_and_alignment(interface_type),
        };
        Ok((
            interface_type,
            field_size,
            field_alignment,
            base_type.struct_name.clone(),
            None,
            array_shape,
        ))
    }

    /// Struct members cannot have variable-length array types. Reuse the
    /// typed constant evaluator, then check the layout's element-count domain
    /// before multiplication by any other dimensions or the element width.
    pub(super) fn parse_struct_array_length(&mut self) -> Result<u32, C0SyntaxError> {
        let expression = self.parse_expression()?;
        let value = evaluate_static_integer_expression(&expression).map_err(|error| {
            self.error_here(match error {
                StaticIntegerEvaluationError::NotConstant => {
                    "struct array lengths require integer constant expressions"
                }
                StaticIntegerEvaluationError::Overflow => {
                    "struct array length integer constant expression overflows"
                }
                StaticIntegerEvaluationError::DivisionByZero => {
                    "struct array length integer constant expression divides by zero"
                }
                StaticIntegerEvaluationError::InvalidShift => {
                    "struct array length integer constant expression has an invalid shift"
                }
                StaticIntegerEvaluationError::OutOfRange => {
                    "struct array length integer constant expression is out of range"
                }
            })
        })?;
        let length = match value {
            StaticIntegerValue::Signed { value, .. } => u32::try_from(value),
            StaticIntegerValue::Unsigned { value, .. } => u32::try_from(value),
        }
        .map_err(|_| self.error_here("struct array length must be positive and fit in 32 bits"))?;
        if length == 0 {
            return Err(self.error_here("struct arrays must have positive length"));
        }
        Ok(length)
    }
}
