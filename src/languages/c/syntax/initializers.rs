//! Parsing array, aggregate and struct initializers, with designators and zero-filled remainders.

use super::*;

impl Parser {
    /// The stores of an automatic scalar array's initializer. When `compact`
    /// (the object is not volatile), the declaration can zero-fill the
    /// array instead of one store per element: the zero fill is returned
    /// with the stores of the elements the initializer writes, which are
    /// then all that follows the declaration. Otherwise every element is
    /// stored, the unwritten ones with the zero initializer.
    pub(super) fn parse_local_array_initializer(
        &mut self,
        name: &str,
        c_type: C0Type,
        array_shape: Option<&[u32]>,
        compact: bool,
    ) -> Result<(Option<C0ZeroFill>, C0Statement), C0SyntaxError> {
        let (length, element_type) = match c_type {
            C0Type::Int32Array(length) => (length, C0Type::Int32),
            C0Type::CharArray(plain, length) => (length, C0Type::Char(plain)),
            C0Type::UInt8Array(length) => (length, C0Type::UInt8),
            C0Type::Int8Array(length) => (length, C0Type::Int8),
            C0Type::Int16Array(length) => (length, C0Type::Int16),
            C0Type::UInt16Array(length) => (length, C0Type::UInt16),
            C0Type::UInt32Array(length) => (length, C0Type::UInt32),
            C0Type::Int64Array(rank, length) => (length, C0Type::Int64(rank)),
            C0Type::Int128Array(length) => (length, C0Type::Int128),
            C0Type::UInt64Array(rank, length) => (length, C0Type::UInt64(rank)),
            C0Type::UInt128Array(length) => (length, C0Type::UInt128),
            C0Type::Float32Array(length) => (length, C0Type::Float32),
            C0Type::Float64Array(length) => (length, C0Type::Float64),
            C0Type::PointerArray(element, rank, length) => {
                (length, pointer_array_element_type(element, rank))
            }
            _ => unreachable!("array initializer called for a scalar type"),
        };
        let zero = zero_initializer(element_type);
        let dimensions = array_shape
            .map(ToOwned::to_owned)
            .unwrap_or_else(|| vec![length]);
        let mut written = Vec::new();
        let mut next = 0u32;
        self.parse_sparse_array_initializer_level(name, &dimensions, 0, &mut written, &mut next)?;
        for (_, value) in &mut written {
            convert_integer_constant(element_type, value);
        }
        let store = |index: u32, value: C0Expression| C0Statement::Store {
            pointer: C0Expression::Add(
                Box::new(C0Expression::Variable(name.to_string())),
                Box::new(C0Expression::Int32Literal(index)),
            ),
            value,
            value_type: Some(element_type),
            lvalue_class: None,
            pointee_constant: false,
            site: C0Site::NONE,
        };
        // The declaration zero-fills the array, and only the written
        // elements that are not the zero initializer are stored after it.
        if compact {
            let written_stores = written
                .iter()
                .map(|(index, value)| store(*index, value.clone()))
                .collect::<Vec<_>>();
            if let Some(zero_fill) = C0ZeroFill::from_element_stores(
                name,
                element_type.abi_size_bytes(),
                length,
                &[store(0, zero.clone())],
            )
            .filter(|_| stores_do_not_read_the_object(name, &written_stores))
            {
                let stores = zero_fill.without_its_own_stores(name, written_stores);
                return Ok((
                    Some(zero_fill),
                    balanced_statement_sequence(stores).unwrap_or(C0Statement::Skip),
                ));
            }
        }

        let mut values = Vec::with_capacity(length as usize);
        for (index, value) in written {
            values.resize(index as usize, zero.clone());
            values.push(value);
        }
        let mut stores = Vec::with_capacity(length as usize);
        for index in 0..length {
            let value = values
                .get(index as usize)
                .cloned()
                .unwrap_or_else(|| zero.clone());
            stores.push(store(index, value));
        }
        Ok((
            None,
            balanced_statement_sequence(stores).unwrap_or(C0Statement::Skip),
        ))
    }

    /// The stores of an automatic struct array's initializer, zero-filled by
    /// the declaration when `compact` as for
    /// [`Self::parse_local_array_initializer`]: every element receives the
    /// zero stores an omitted element would, and only the listed fields that
    /// are not those zeros are stored after it.
    pub(super) fn parse_local_struct_array_initializer(
        &mut self,
        name: &str,
        struct_name: &str,
        array_shape: &[u32],
        compact: bool,
    ) -> Result<(Option<C0ZeroFill>, C0Statement), C0SyntaxError> {
        if self.peek() != Some(&Token::LBrace) {
            return Err(self.error_here(
                "local struct array elements require nested `{...}` initializer groups",
            ));
        }
        let element_width = self
            .structs
            .get(struct_name)
            .expect("validated local struct array has a layout")
            .size_bytes;
        let zero_fill = compact
            .then(|| {
                let count = array_shape
                    .iter()
                    .try_fold(1u32, |count, dimension| count.checked_mul(*dimension))?;
                C0ZeroFill::from_element_stores(
                    name,
                    element_width,
                    count,
                    &self.zero_struct_initializer_level(
                        C0Expression::Variable(name.to_string()),
                        struct_name,
                    ),
                )
            })
            .flatten();
        let start = self.position;
        if let Some(zero_fill) = zero_fill {
            let stores = self.parse_embedded_struct_array_initializer_level(
                C0Expression::Variable(name.to_string()),
                struct_name,
                array_shape,
                0,
                0,
                element_width,
                false,
            )?;
            if stores_do_not_read_the_object(name, &stores) {
                let stores = zero_fill.without_its_own_stores(name, stores);
                return Ok((
                    Some(zero_fill),
                    balanced_statement_sequence(stores).unwrap_or(C0Statement::Skip),
                ));
            }
            // An initializer that reads the array keeps every store in
            // element order: parse it again with the omitted elements' zeros.
            self.position = start;
        }
        let stores = self.parse_embedded_struct_array_initializer_level(
            C0Expression::Variable(name.to_string()),
            struct_name,
            array_shape,
            0,
            0,
            element_width,
            true,
        )?;
        Ok((
            None,
            balanced_statement_sequence(stores).unwrap_or(C0Statement::Skip),
        ))
    }

    /// One brace level of a nested array initializer, appended to `values`
    /// with every element it leaves out as `zero`.
    pub(super) fn parse_array_initializer_level(
        &mut self,
        name: &str,
        dimensions: &[u32],
        depth: usize,
        values: &mut Vec<C0Expression>,
        zero: &C0Expression,
    ) -> Result<(), C0SyntaxError> {
        let mut next = u32::try_from(values.len()).expect("validated array initializer length");
        let mut written = Vec::new();
        self.parse_sparse_array_initializer_level(
            name,
            dimensions,
            depth,
            &mut written,
            &mut next,
        )?;
        for (index, value) in written {
            values.resize(index as usize, zero.clone());
            values.push(value);
        }
        values.resize(next as usize, zero.clone());
        Ok(())
    }

    /// One brace level of a nested array initializer whose first element is
    /// flattened element `next`: each written element is appended to
    /// `values` with its flattened index, and `next` is left past the
    /// level's last element, written or not, so what the level leaves out
    /// costs nothing.
    pub(super) fn parse_sparse_array_initializer_level(
        &mut self,
        name: &str,
        dimensions: &[u32],
        depth: usize,
        values: &mut Vec<(u32, C0Expression)>,
        next: &mut u32,
    ) -> Result<(), C0SyntaxError> {
        let child_width = dimensions[depth + 1..]
            .iter()
            .copied()
            .fold(1u32, |width, dimension| {
                width
                    .checked_mul(dimension)
                    .expect("validated array shape has a representable width")
            });
        let child_count = dimensions[depth];
        let start = *next;
        self.expect(Token::LBrace)?;
        let mut children = 0u32;
        if self.peek() != Some(&Token::RBrace) {
            loop {
                if children == child_count {
                    return Err(self
                        .error_here(format!("too many initializers for `{name}[{child_count}]`")));
                }
                if depth + 1 == dimensions.len() {
                    values.push((*next, self.parse_expression()?));
                    *next += 1;
                } else {
                    if self.peek() != Some(&Token::LBrace) {
                        return Err(self.error_here(format!(
                            "nested initializer for `{name}` expects `{}` groups",
                            dimensions.len() - depth - 1
                        )));
                    }
                    self.parse_sparse_array_initializer_level(
                        name,
                        dimensions,
                        depth + 1,
                        values,
                        next,
                    )?;
                }
                children += 1;
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
                            "expected `,` or `}}` in `{name}` initializer, got {}",
                            token.describe()
                        )));
                    }
                    None => {
                        return Err(self.error_here(format!(
                            "expected `,` or `}}` in `{name}` initializer, got end of input"
                        )));
                    }
                }
            }
        }
        self.expect(Token::RBrace)?;

        let expected = child_count
            .checked_mul(child_width)
            .expect("validated array shape has a representable length");
        *next = start
            .checked_add(expected)
            .expect("validated array shape has a representable length");
        Ok(())
    }

    pub(super) fn parse_aggregate_initializer(
        &mut self,
        object_name: &str,
        struct_name: &str,
    ) -> Result<Vec<C0AggregateInitializer>, C0SyntaxError> {
        self.parse_aggregate_initializer_level(object_name, struct_name, 0)
    }

    pub(super) fn parse_aggregate_array_initializer(
        &mut self,
        object_name: &str,
        struct_name: &str,
        layout: &C0StructLayout,
        length: u32,
    ) -> Result<Vec<C0AggregateInitializer>, C0SyntaxError> {
        self.parse_aggregate_array_initializer_with_bound(
            object_name,
            struct_name,
            layout,
            Some(length),
        )
        .map(|(_, initializer)| initializer)
    }

    pub(super) fn parse_aggregate_array_initializer_with_bound(
        &mut self,
        object_name: &str,
        struct_name: &str,
        layout: &C0StructLayout,
        length: Option<u32>,
    ) -> Result<(u32, Vec<C0AggregateInitializer>), C0SyntaxError> {
        self.expect(Token::LBrace)?;
        let mut initializers = Vec::new();
        let mut next_element_index = 0u32;
        if self.peek() != Some(&Token::RBrace) {
            loop {
                let element_index = if self.peek() == Some(&Token::LBracket) {
                    let length = length.ok_or_else(|| {
                        self.error_here(
                            "inferred aggregate arrays require positional element initializers",
                        )
                    })?;
                    self.position += 1;
                    let index = self.parse_aggregate_array_designator(object_name, length)?;
                    self.expect(Token::Equal)?;
                    next_element_index = index
                        .checked_add(1)
                        .expect("validated aggregate array designator index");
                    index
                } else {
                    if self.peek() == Some(&Token::Dot) {
                        return Err(self.error_here(
                            "aggregate array initializers support only array index designators",
                        ));
                    }
                    let index = next_element_index;
                    next_element_index = next_element_index.checked_add(1).ok_or_else(|| {
                        self.error_here("aggregate array initializer length overflows")
                    })?;
                    index
                };
                if length.is_some_and(|length| element_index >= length) {
                    return Err(self.error_here(format!(
                        "too many initializers for aggregate array `{object_name}`"
                    )));
                }
                if self.peek() != Some(&Token::LBrace) {
                    return Err(self.error_here(
                        "aggregate array elements require nested `{...}` initializer groups",
                    ));
                }
                let base_offset = element_index
                    .checked_mul(layout.size_bytes())
                    .ok_or_else(|| self.error_here("aggregate array initializer size overflows"))?;
                base_offset
                    .checked_add(layout.size_bytes())
                    .ok_or_else(|| self.error_here("aggregate array initializer size overflows"))?;
                initializers.extend(self.parse_aggregate_initializer_level(
                    object_name,
                    struct_name,
                    base_offset,
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
                            "expected `,` or `}}` in aggregate array initializer for `{object_name}`, got {}",
                            token.describe()
                        )));
                    }
                    None => {
                        return Err(self.error_here(format!(
                            "expected `,` or `}}` in aggregate array initializer for `{object_name}`, got end of input"
                        )));
                    }
                }
            }
        }
        self.expect(Token::RBrace)?;
        let length = length.unwrap_or(next_element_index);
        if length == 0 {
            return Err(
                self.error_here("inferred aggregate array requires a non-empty initializer")
            );
        }
        Ok((length, initializers))
    }

    pub(super) fn parse_aggregate_array_designator(
        &mut self,
        object_name: &str,
        length: u32,
    ) -> Result<u32, C0SyntaxError> {
        let index = match self.next() {
            Some(Token::Number(number)) => {
                let magnitude = parse_integer_literal_magnitude(&number).map_err(|reason| {
                    self.error_at_previous(format!(
                        "invalid aggregate array designator index `{number}`: {reason}"
                    ))
                })?;
                u32::try_from(magnitude).map_err(|_| {
                    self.error_at_previous(format!(
                        "aggregate array designator index `{number}` is out of range"
                    ))
                })?
            }
            Some(Token::CharLiteral(value)) => self.character_designator_index(value)?,
            Some(token) => {
                return Err(self.error_at_previous(format!(
                    "aggregate array designators currently require integer literals, got {}",
                    token.describe()
                )));
            }
            None => {
                return Err(self.error_here(
                    "aggregate array designators currently require an integer literal",
                ));
            }
        };
        self.expect(Token::RBracket)?;
        if index >= length {
            return Err(self.error_here(format!(
                "aggregate array designator index `{index}` is out of bounds for `{object_name}[{length}]`"
            )));
        }
        Ok(index)
    }

    pub(super) fn parse_aggregate_initializer_level(
        &mut self,
        object_name: &str,
        struct_name: &str,
        base_offset: u32,
    ) -> Result<Vec<C0AggregateInitializer>, C0SyntaxError> {
        let mut fields = self
            .structs
            .get(struct_name)
            .expect("validated aggregate initializer has a layout")
            .fields
            .iter()
            .map(|(name, field)| (name.clone(), field.clone()))
            .collect::<Vec<_>>();
        fields.sort_by_key(|(_, field)| field.offset_bytes);

        self.expect(Token::LBrace)?;
        let mut initializers = Vec::new();
        let mut next_field_index = 0usize;
        if self.peek() != Some(&Token::RBrace) {
            loop {
                let field_index = if self.peek() == Some(&Token::Dot) {
                    self.position += 1;
                    let field_name = self.expect_ident("aggregate field name")?;
                    self.expect(Token::Equal)?;
                    let Some(index) = fields.iter().position(|(name, _)| name == &field_name)
                    else {
                        return Err(self.error_here(format!(
                            "unknown field `{field_name}` in `struct {struct_name}` initializer"
                        )));
                    };
                    next_field_index = index
                        .checked_add(1)
                        .expect("validated aggregate field index");
                    index
                } else {
                    if self.peek() == Some(&Token::LBracket) {
                        return Err(self.error_here(
                            "struct aggregate initializers support only field designators",
                        ));
                    }
                    let index = next_field_index;
                    next_field_index = next_field_index
                        .checked_add(1)
                        .expect("validated aggregate field index");
                    index
                };
                let Some((_, field)) = fields.get(field_index) else {
                    return Err(self
                        .error_here(format!("too many initializers for `struct {struct_name}`")));
                };
                initializers.extend(self.parse_aggregate_initializer_field(
                    object_name,
                    base_offset,
                    field,
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
                            "expected `,` or `}}` in aggregate initializer for `{object_name}`, got {}",
                            token.describe()
                        )));
                    }
                    None => {
                        return Err(self.error_here(format!(
                            "expected `,` or `}}` in aggregate initializer for `{object_name}`, got end of input"
                        )));
                    }
                }
            }
        }
        self.expect(Token::RBrace)?;
        Ok(initializers)
    }

    pub(super) fn parse_aggregate_initializer_field(
        &mut self,
        object_name: &str,
        base_offset: u32,
        field: &C0StructField,
    ) -> Result<Vec<C0AggregateInitializer>, C0SyntaxError> {
        let field_offset = base_offset
            .checked_add(field.offset_bytes)
            .expect("validated aggregate initializer field offset");
        if let Some(element_width) = field.array_element_width {
            let nested_name = field
                .struct_name
                .as_deref()
                .expect("embedded struct array has a struct name");
            let dimensions = field
                .array_shape
                .as_deref()
                .expect("embedded struct array has a shape");
            if self.peek() != Some(&Token::LBrace) {
                return Err(self.error_here(
                    "embedded struct array initializers require nested `{...}` groups",
                ));
            }
            return self.parse_embedded_struct_array_aggregate_initializer_level(
                object_name,
                nested_name,
                dimensions,
                0,
                0,
                field_offset,
                element_width,
            );
        }
        if field.c_type == C0Type::Int32
            && let Some(nested_name) = field.struct_name.as_deref()
        {
            if self.peek() != Some(&Token::LBrace) {
                return Err(
                    self.error_here("embedded struct initializers require a nested `{...}` group")
                );
            }
            return self.parse_aggregate_initializer_level(object_name, nested_name, field_offset);
        }

        if let Some((element_type, dimensions)) = struct_scalar_array_shape(field) {
            if self.peek() != Some(&Token::LBrace) {
                return Err(self.error_here(
                    "inline scalar array initializers require a nested `{...}` group",
                ));
            }
            let zero = zero_initializer(element_type);
            let mut values = Vec::new();
            self.parse_array_initializer_level(
                "aggregate field",
                &dimensions,
                0,
                &mut values,
                &zero,
            )?;
            let mut initializers = Vec::with_capacity(values.len());
            for (index, value) in values.into_iter().enumerate() {
                validate_aggregate_initializer(self, element_type, &value)?;
                let offset = field_offset
                    .checked_add(
                        u32::try_from(index)
                            .expect("validated aggregate initializer index")
                            .checked_mul(element_type.abi_size_bytes())
                            .expect("validated aggregate initializer offset"),
                    )
                    .expect("validated aggregate initializer offset");
                initializers.push(C0AggregateInitializer::new(offset, element_type, value));
            }
            return Ok(initializers);
        }

        let mut value = self.parse_expression()?;
        // A callback field takes a function address or the null pointer. The
        // field's own signature is the expected one, so the check is the same
        // one an assignment through a pointer already performs.
        if matches!(field.c_type, C0Type::FunctionPointer(_)) {
            let expected = field
                .function_pointer_signature
                .as_ref()
                .expect("a function-pointer field carries its signature");
            self.validate_function_pointer_value(expected, &value)?;
            if !matches!(
                value,
                C0Expression::Int32Literal(0) | C0Expression::FunctionAddress(_)
            ) {
                return Err(self.error_here(
                    "aggregate callback initializers currently support only a function address or the null pointer literal",
                ));
            }
            return Ok(vec![C0AggregateInitializer::new(
                field_offset,
                field.c_type,
                value,
            )]);
        }
        self.reject_discarded_const_pointer(field.c_type, field.pointee_constant, &mut value)?;
        validate_aggregate_initializer(self, field.c_type, &value)?;
        Ok(vec![C0AggregateInitializer::new(
            field_offset,
            field.c_type,
            value,
        )])
    }

    pub(super) fn parse_embedded_struct_array_aggregate_initializer_level(
        &mut self,
        object_name: &str,
        struct_name: &str,
        dimensions: &[u32],
        depth: usize,
        flat_prefix: u32,
        element_offset: u32,
        element_width: u32,
    ) -> Result<Vec<C0AggregateInitializer>, C0SyntaxError> {
        let child_count = dimensions[depth];
        let child_width = dimensions[depth + 1..]
            .iter()
            .copied()
            .fold(1u32, |width, dimension| {
                width
                    .checked_mul(dimension)
                    .expect("validated embedded struct array initializer width")
            });
        self.expect(Token::LBrace)?;
        let mut initializers = Vec::new();
        let mut child_index = 0u32;
        if self.peek() != Some(&Token::RBrace) {
            loop {
                if child_index == child_count {
                    return Err(
                        self.error_here("too many initializers for an embedded struct array")
                    );
                }
                let flat_index = flat_prefix
                    .checked_add(
                        child_index
                            .checked_mul(child_width)
                            .expect("validated embedded struct array initializer index"),
                    )
                    .expect("validated embedded struct array initializer index");
                let child_offset = element_offset
                    .checked_add(
                        flat_index
                            .checked_mul(element_width)
                            .expect("validated embedded struct array initializer offset"),
                    )
                    .expect("validated embedded struct array initializer offset");
                if depth + 1 == dimensions.len() {
                    if self.peek() != Some(&Token::LBrace) {
                        return Err(self.error_here(
                            "embedded struct array elements require nested `{...}` groups",
                        ));
                    }
                    initializers.extend(self.parse_aggregate_initializer_level(
                        object_name,
                        struct_name,
                        child_offset,
                    )?);
                } else {
                    if self.peek() != Some(&Token::LBrace) {
                        return Err(self.error_here(
                            "nested embedded struct array initializers require `{...}` groups",
                        ));
                    }
                    initializers.extend(
                        self.parse_embedded_struct_array_aggregate_initializer_level(
                            object_name,
                            struct_name,
                            dimensions,
                            depth + 1,
                            flat_index,
                            element_offset,
                            element_width,
                        )?,
                    );
                }
                child_index += 1;
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
                            "expected `,` or `}}` in embedded struct array initializer for `{object_name}`, got {}",
                            token.describe()
                        )));
                    }
                    None => {
                        return Err(self.error_here(format!(
                            "expected `,` or `}}` in embedded struct array initializer for `{object_name}`, got end of input"
                        )));
                    }
                }
            }
        }
        self.expect(Token::RBrace)?;
        Ok(initializers)
    }

    pub(super) fn parse_struct_value_initializer(
        &mut self,
        target: &str,
        struct_name: &str,
    ) -> Result<C0Statement, C0SyntaxError> {
        let stores = self.parse_struct_initializer_level(
            C0Expression::Variable(target.to_string()),
            struct_name,
        )?;
        Ok(balanced_statement_sequence(stores).unwrap_or(C0Statement::Skip))
    }

    pub(super) fn parse_struct_initializer_level(
        &mut self,
        target_pointer: C0Expression,
        struct_name: &str,
    ) -> Result<Vec<C0Statement>, C0SyntaxError> {
        let mut fields = self
            .structs
            .get(struct_name)
            .expect("validated struct initializer has a layout")
            .fields
            .values()
            .cloned()
            .collect::<Vec<_>>();
        // `fields` is a BTreeMap for name lookup, but C initializer order is
        // declaration order. ABI offsets are already assigned in declaration
        // order, so they provide the stable source-order key here.
        fields.sort_by_key(|field| field.offset_bytes);

        self.expect(Token::LBrace)?;
        let mut stores = Vec::new();
        let mut field_index = 0usize;
        let mut has_designated_initializer = false;
        if self.peek() != Some(&Token::RBrace) {
            loop {
                if self.peek() == Some(&Token::Dot) {
                    has_designated_initializer = true;
                    let (designated_index, parent_pointer, field) = self
                        .parse_struct_field_designator(
                            target_pointer.clone(),
                            struct_name,
                            &fields,
                        )?;
                    stores.extend(self.parse_struct_initializer_field(parent_pointer, &field)?);
                    // C continues positional initialization after the
                    // top-level field selected by a designator. Nested field
                    // designators therefore advance past their outer field.
                    field_index = designated_index + 1;
                } else {
                    if self.peek() == Some(&Token::LBracket) {
                        return Err(self.error_here(
                            "array designators in struct initializers are not supported",
                        ));
                    }
                    let Some(field) = fields.get(field_index) else {
                        return Err(self.error_here(format!(
                            "too many initializers for `struct {struct_name}`"
                        )));
                    };
                    stores.extend(
                        self.parse_struct_initializer_field(target_pointer.clone(), field)?,
                    );
                    field_index += 1;
                }
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
                            "expected `,` or `}}` in `struct {struct_name}` initializer, got {}",
                            token.describe()
                        )));
                    }
                    None => {
                        return Err(self.error_here(format!(
                            "expected `,` or `}}` in `struct {struct_name}` initializer, got end of input"
                        )));
                    }
                }
            }
        }
        self.expect(Token::RBrace)?;

        if has_designated_initializer {
            // A designated initializer may arrive out of declaration order or
            // initialize only a nested leaf. Start from a complete zero value
            // so every omitted member has the same semantics as a positional
            // initializer, then apply explicit stores in source order.
            let mut zero_stores =
                self.zero_struct_initializer_level(target_pointer.clone(), struct_name);
            zero_stores.extend(stores);
            stores = zero_stores;
        } else {
            for field in fields.iter().skip(field_index) {
                stores.extend(self.zero_struct_initializer_field(target_pointer.clone(), field));
            }
        }
        Ok(stores)
    }

    /// Parses one or more `.field` designators for a struct initializer. The
    /// returned pointer addresses the parent of the final field, so the
    /// ordinary field initializer path can retain all of its nested aggregate
    /// and scalar-array handling.
    pub(super) fn parse_struct_field_designator(
        &mut self,
        target_pointer: C0Expression,
        struct_name: &str,
        root_fields: &[C0StructField],
    ) -> Result<(usize, C0Expression, C0StructField), C0SyntaxError> {
        let mut current_struct_name = struct_name.to_string();
        let mut parent_pointer = target_pointer;
        let mut root_index = None;

        loop {
            self.expect(Token::Dot)?;
            let field_name = self.expect_ident("struct field designator")?;
            let layout = self.structs.get(&current_struct_name).ok_or_else(|| {
                self.error_here(format!(
                    "unknown struct declaration `{current_struct_name}`"
                ))
            })?;
            let field = layout.fields.get(&field_name).cloned().ok_or_else(|| {
                self.error_here(format!(
                    "struct `{current_struct_name}` has no field `{field_name}`"
                ))
            })?;

            if root_index.is_none() {
                root_index = root_fields
                    .iter()
                    .position(|candidate| candidate.offset_bytes == field.offset_bytes);
            }

            if self.peek() == Some(&Token::LBracket) {
                return Err(
                    self.error_here("array designators in struct initializers are not supported")
                );
            }
            if self.peek() == Some(&Token::Dot) {
                if field.array_element_width.is_some()
                    || field.c_type != C0Type::Int32
                    || field.struct_name.is_none()
                {
                    return Err(self
                        .error_here("nested field designators require an embedded struct field"));
                }
                parent_pointer = offset_field_pointer(parent_pointer, field.offset_bytes);
                current_struct_name = field
                    .struct_name
                    .expect("embedded struct designator has a struct name");
                continue;
            }

            self.expect(Token::Equal)?;
            let root_index = root_index.expect("root field designator belongs to the root layout");
            return Ok((root_index, parent_pointer, field));
        }
    }

    pub(super) fn parse_struct_initializer_field(
        &mut self,
        target_pointer: C0Expression,
        field: &C0StructField,
    ) -> Result<Vec<C0Statement>, C0SyntaxError> {
        let field_pointer = offset_field_pointer(target_pointer, field.offset_bytes);
        if let Some(element_width) = field.array_element_width {
            let struct_name = field
                .struct_name
                .as_deref()
                .expect("embedded struct array has a struct name");
            let shape = field
                .array_shape
                .as_deref()
                .expect("embedded struct array has a shape");
            if self.peek() != Some(&Token::LBrace) {
                return Err(self.error_here(
                    "embedded struct array initializers require nested `{...}` groups",
                ));
            }
            return self.parse_embedded_struct_array_initializer_level(
                field_pointer,
                struct_name,
                shape,
                0,
                0,
                element_width,
                true,
            );
        }
        if field.c_type == C0Type::Int32
            && let Some(struct_name) = field.struct_name.as_deref()
        {
            if self.peek() != Some(&Token::LBrace) {
                return Err(
                    self.error_here("embedded struct initializers require a nested `{...}` group")
                );
            }
            return self.parse_struct_initializer_level(field_pointer, struct_name);
        }

        if let Some((element_type, dimensions)) = struct_scalar_array_shape(field) {
            if self.peek() != Some(&Token::LBrace) {
                return Err(self.error_here(
                    "inline scalar array initializers require a nested `{...}` group",
                ));
            }
            let mut values = Vec::new();
            let zero = zero_initializer(element_type);
            self.parse_array_initializer_level("struct field", &dimensions, 0, &mut values, &zero)?;
            return Ok(values
                .into_iter()
                .enumerate()
                .map(|(index, value)| C0Statement::Store {
                    pointer: offset_field_pointer(
                        field_pointer.clone(),
                        u32::try_from(index)
                            .expect("validated struct array initializer index")
                            .checked_mul(element_type.abi_size_bytes())
                            .expect("validated struct array initializer offset"),
                    ),
                    value,
                    value_type: Some(element_type),
                    lvalue_class: None,
                    pointee_constant: false,
                    site: C0Site::NONE,
                })
                .collect());
        }

        let mut value = self.parse_expression()?;
        self.reject_discarded_const_pointer(field.c_type, field.pointee_constant, &mut value)?;
        Ok(vec![C0Statement::Store {
            pointer: field_pointer,
            value,
            value_type: Some(field.c_type),
            lvalue_class: None,
            pointee_constant: field.pointee_constant,
            site: C0Site::NONE,
        }])
    }

    /// The stores of one brace level of a struct array's initializer: the
    /// elements it lists, and, when `zero_omitted`, the zero stores of every
    /// element it leaves out. A caller whose declaration zero-fills the array
    /// passes `false`, so an omitted element costs nothing.
    pub(super) fn parse_embedded_struct_array_initializer_level(
        &mut self,
        target_pointer: C0Expression,
        struct_name: &str,
        dimensions: &[u32],
        depth: usize,
        flat_prefix: u32,
        element_width: u32,
        zero_omitted: bool,
    ) -> Result<Vec<C0Statement>, C0SyntaxError> {
        let child_count = dimensions[depth];
        self.expect(Token::LBrace)?;
        let mut stores = Vec::new();
        let mut next_child_index = 0u32;
        let mut initialized_children = BTreeSet::new();
        if self.peek() != Some(&Token::RBrace) {
            loop {
                let child_index = if self.peek() == Some(&Token::LBracket) {
                    self.position += 1;
                    let index =
                        self.parse_local_struct_array_designator(struct_name, depth, child_count)?;
                    self.expect(Token::Equal)?;
                    next_child_index = index
                        .checked_add(1)
                        .expect("validated local struct array designator index");
                    index
                } else {
                    let index = next_child_index;
                    next_child_index = next_child_index
                        .checked_add(1)
                        .expect("validated local struct array initializer index");
                    index
                };
                if child_index >= child_count {
                    return Err(
                        self.error_here("too many initializers for an embedded struct array")
                    );
                }
                initialized_children.insert(child_index);
                let flat_index = flat_prefix
                    .checked_mul(child_count)
                    .and_then(|index| index.checked_add(child_index))
                    .expect("validated embedded struct array initializer index");
                if depth + 1 == dimensions.len() {
                    if self.peek() != Some(&Token::LBrace) {
                        return Err(self.error_here(
                            "embedded struct array elements require nested `{...}` groups",
                        ));
                    }
                    stores.extend(
                        self.parse_struct_initializer_level(
                            offset_field_pointer(
                                target_pointer.clone(),
                                flat_index
                                    .checked_mul(element_width)
                                    .expect("validated embedded struct array initializer offset"),
                            ),
                            struct_name,
                        )?,
                    );
                } else {
                    if self.peek() != Some(&Token::LBrace) {
                        return Err(self.error_here(
                            "nested embedded struct array initializers require `{...}` groups",
                        ));
                    }
                    stores.extend(self.parse_embedded_struct_array_initializer_level(
                        target_pointer.clone(),
                        struct_name,
                        dimensions,
                        depth + 1,
                        flat_index,
                        element_width,
                        zero_omitted,
                    )?);
                }
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
                            "expected `,` or `}}` in embedded struct array initializer, got {}",
                            token.describe()
                        )));
                    }
                    None => {
                        return Err(self.error_here(
                            "expected `,` or `}` in embedded struct array initializer, got end of input",
                        ));
                    }
                }
            }
        }
        self.expect(Token::RBrace)?;

        if !zero_omitted {
            return Ok(stores);
        }
        for child_index in 0..child_count {
            if initialized_children.contains(&child_index) {
                continue;
            }
            let flat_index = flat_prefix
                .checked_mul(child_count)
                .and_then(|index| index.checked_add(child_index))
                .expect("validated embedded struct array initializer index");
            if depth + 1 == dimensions.len() {
                stores.extend(
                    self.zero_struct_initializer_level(
                        offset_field_pointer(
                            target_pointer.clone(),
                            flat_index
                                .checked_mul(element_width)
                                .expect("validated embedded struct array initializer offset"),
                        ),
                        struct_name,
                    ),
                );
            } else {
                stores.extend(self.zero_embedded_struct_array_initializer_level(
                    target_pointer.clone(),
                    struct_name,
                    dimensions,
                    depth + 1,
                    flat_index,
                    element_width,
                ));
            }
        }
        Ok(stores)
    }

    pub(super) fn parse_local_struct_array_designator(
        &mut self,
        struct_name: &str,
        depth: usize,
        length: u32,
    ) -> Result<u32, C0SyntaxError> {
        let index = match self.next() {
            Some(Token::Number(number)) => {
                let magnitude = parse_integer_literal_magnitude(&number).map_err(|reason| {
                    self.error_at_previous(format!(
                        "invalid local struct array designator index `{number}`: {reason}"
                    ))
                })?;
                u32::try_from(magnitude).map_err(|_| {
                    self.error_at_previous(format!(
                        "local struct array designator index `{number}` is out of range"
                    ))
                })?
            }
            Some(Token::CharLiteral(value)) => self.character_designator_index(value)?,
            Some(token) => {
                return Err(self.error_at_previous(format!(
                    "local struct array designators currently require integer literals, got {}",
                    token.describe()
                )));
            }
            None => {
                return Err(self.error_here(
                    "local struct array designators currently require an integer literal",
                ));
            }
        };
        self.expect(Token::RBracket)?;
        if index >= length {
            return Err(self.error_here(format!(
                "local struct array designator index `{index}` is out of bounds for `struct {struct_name}` dimension {depth} of length {length}"
            )));
        }
        Ok(index)
    }

    pub(super) fn zero_struct_initializer_level(
        &self,
        target_pointer: C0Expression,
        struct_name: &str,
    ) -> Vec<C0Statement> {
        let mut fields = self
            .structs
            .get(struct_name)
            .expect("validated struct initializer has a layout")
            .fields
            .values()
            .cloned()
            .collect::<Vec<_>>();
        fields.sort_by_key(|field| field.offset_bytes);
        fields
            .iter()
            .flat_map(|field| self.zero_struct_initializer_field(target_pointer.clone(), field))
            .collect()
    }

    pub(super) fn zero_struct_initializer_field(
        &self,
        target_pointer: C0Expression,
        field: &C0StructField,
    ) -> Vec<C0Statement> {
        let field_pointer = offset_field_pointer(target_pointer, field.offset_bytes);
        if let Some(element_width) = field.array_element_width {
            let struct_name = field
                .struct_name
                .as_deref()
                .expect("embedded struct array has a struct name");
            let shape = field
                .array_shape
                .as_deref()
                .expect("embedded struct array has a shape");
            return self.zero_embedded_struct_array_initializer_level(
                field_pointer,
                struct_name,
                shape,
                0,
                0,
                element_width,
            );
        }
        if field.c_type == C0Type::Int32
            && let Some(struct_name) = field.struct_name.as_deref()
        {
            return self.zero_struct_initializer_level(field_pointer, struct_name);
        }

        if let Some((element_type, dimensions)) = struct_scalar_array_shape(field) {
            let element_count = dimensions.iter().product::<u32>();
            return (0..element_count)
                .map(|index| C0Statement::Store {
                    pointer: offset_field_pointer(
                        field_pointer.clone(),
                        index
                            .checked_mul(element_type.abi_size_bytes())
                            .expect("validated struct array initializer offset"),
                    ),
                    value: zero_initializer_value(element_type),
                    value_type: Some(element_type),
                    lvalue_class: None,
                    pointee_constant: false,
                    site: C0Site::NONE,
                })
                .collect();
        }

        vec![C0Statement::Store {
            pointer: field_pointer,
            value: zero_initializer_value(field.c_type),
            value_type: Some(field.c_type),
            lvalue_class: None,
            pointee_constant: field.pointee_constant,
            site: C0Site::NONE,
        }]
    }

    pub(super) fn zero_embedded_struct_array_initializer_level(
        &self,
        target_pointer: C0Expression,
        struct_name: &str,
        dimensions: &[u32],
        depth: usize,
        flat_prefix: u32,
        element_width: u32,
    ) -> Vec<C0Statement> {
        let child_count = dimensions[depth];
        let mut stores = Vec::new();
        for child_index in 0..child_count {
            let flat_index = flat_prefix
                .checked_mul(child_count)
                .and_then(|index| index.checked_add(child_index))
                .expect("validated embedded struct array initializer index");
            if depth + 1 == dimensions.len() {
                stores.extend(
                    self.zero_struct_initializer_level(
                        offset_field_pointer(
                            target_pointer.clone(),
                            flat_index
                                .checked_mul(element_width)
                                .expect("validated embedded struct array initializer offset"),
                        ),
                        struct_name,
                    ),
                );
            } else {
                stores.extend(self.zero_embedded_struct_array_initializer_level(
                    target_pointer.clone(),
                    struct_name,
                    dimensions,
                    depth + 1,
                    flat_index,
                    element_width,
                ));
            }
        }
        stores
    }
}
