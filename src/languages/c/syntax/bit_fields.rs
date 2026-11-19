//! Named int bit-fields in automatic records and fixed local pointers to them.
use super::bit_field_layout::IntBitField;
use super::*;
use std::num::NonZeroU8;
use std::sync::Arc;

/// One named member at its target ABI position.
#[derive(Clone, Copy, Debug)]
pub(super) struct Slice {
    placement: IntBitField,
    signed: bool,
}

#[derive(Clone, Copy, Debug)]
enum Member {
    Bits(Slice),
    Scalar {
        offset: u32,
        ty: InterfaceType,
        width: u32,
    },
}

impl Member {
    fn start_bit(self) -> u64 {
        match self {
            Self::Bits(field) => field.placement.start_bit(),
            Self::Scalar { offset, .. } => 8 * u64::from(offset),
        }
    }
}

#[derive(Debug)]
pub(super) struct BitFieldRecord {
    names: BTreeMap<String, usize>,
    fields: Vec<Member>,
    pub(super) storage: RecordLayout,
    supports_local_objects: bool,
}

impl BitFieldRecord {
    pub(super) fn size_bytes(&self) -> u32 {
        self.storage.size_bytes
    }
}

#[derive(Clone, Debug)]
pub(super) struct LocalBitFields {
    record: Arc<BitFieldRecord>,
    storage: BindingName,
    /// A runtime binding is retained even though its pointee is fixed by
    /// syntax. Reading it still checks that C executed its initializer.
    pointer: Option<BindingName>,
    read_only: bool,
}

impl LocalBitFields {
    fn address(&self) -> CExpression {
        match &self.pointer {
            Some(pointer) => CExpression::Variable(pointer.clone()),
            None => CExpression::AddressOf(Box::new(CExpression::Variable(self.storage.clone()))),
        }
    }

    pub(super) fn source_pointer(&self) -> CExpression {
        let mut pointer = scalar_cast(self.address(), InterfaceType::Int32Pointer);
        let CExpression::Cast {
            struct_name,
            pointee_constant,
            ..
        } = &mut pointer
        else {
            unreachable!("pointer cast");
        };
        *struct_name = self
            .record
            .storage
            .class
            .as_ref()
            .map(|class| class.tag().to_owned());
        *pointee_constant = self.read_only;
        pointer
    }

    pub(super) fn is_pointer(&self) -> bool {
        self.pointer.is_some()
    }

    pub(super) fn size_bytes(&self) -> u32 {
        self.record.storage.size_bytes
    }

    fn byte_address(&self, offset: u32) -> CExpression {
        CExpression::PointerOffsetBytes {
            pointer: Box::new(self.address()),
            bytes: offset,
        }
    }

    fn scalar_pointer(&self, offset: u32, width: u32) -> CExpression {
        let pointer = CExpression::Subobject {
            pointer: Box::new(self.byte_address(offset)),
            width,
        };
        if self.read_only {
            let mut view = scalar_cast(pointer, InterfaceType::UInt8Pointer);
            let CExpression::Cast {
                pointee_constant, ..
            } = &mut view
            else {
                unreachable!("pointer cast");
            };
            *pointee_constant = true;
            view
        } else {
            pointer
        }
    }

    fn scalar_class(
        &self,
        ty: InterfaceType,
    ) -> Option<crate::kernel::effective_type::CAccessClass> {
        let class = self.record.storage.class.as_ref()?.clone();
        Some(crate::kernel::effective_type::CAccessClass::member(
            class,
            ty.access_class(),
        ))
    }

    fn read_member(&self, member: Member) -> CExpression {
        match member {
            Member::Bits(field) => self.read(field),
            Member::Scalar { offset, ty, width } => CExpression::Field {
                pointer: Box::new(self.scalar_pointer(offset, width)),
                field_type: ty,
                pointee_constant: false,
                field_struct_name: None,
                function_pointer_signature: None,
                array_shape: None,
                source: None,
                access_class: self.scalar_class(ty),
            },
        }
    }

    fn scalar_store(
        &self,
        offset: u32,
        ty: InterfaceType,
        width: u32,
        value: CExpression,
    ) -> CStatement {
        CStatement::Store {
            pointer: self.scalar_pointer(offset, width),
            value,
            value_type: Some(ty),
            lvalue_class: self.scalar_class(ty),
            pointee_constant: self.read_only,
            site: CSite::NONE,
        }
    }

    fn read(&self, field: Slice) -> CExpression {
        let mut selected = None;
        for (offset, mask) in field.byte_masks() {
            crate::instrumentation::record_deterministic_work(1);
            let byte = CExpression::Field {
                pointer: Box::new(self.byte_address(offset)),
                field_type: InterfaceType::UInt8,
                pointee_constant: false,
                field_struct_name: None,
                function_pointer_signature: None,
                array_shape: None,
                source: None,
                access_class: Some(crate::kernel::effective_type::CAccessClass::BitFieldByte(
                    mask,
                )),
            };
            let bits = scalar_cast(byte, InterfaceType::UInt32);
            let positioned = CExpression::ShiftLeft(
                Box::new(bits),
                Box::new(CExpression::Int32Literal(8 * (offset % 4))),
            );
            selected = Some(match selected {
                None => positioned,
                Some(previous) => CExpression::BitwiseOr(Box::new(previous), Box::new(positioned)),
            });
        }
        let shifted = CExpression::ShiftRight(
            Box::new(selected.expect("nonempty field")),
            Box::new(CExpression::Int32Literal(field.placement.shift_in_word())),
        );
        field.promote(shifted)
    }

    fn store_bytes(
        &self,
        bytes: impl Iterator<Item = (u32, NonZeroU8)>,
        mut value_at: impl FnMut(u32) -> CExpression,
    ) -> impl Iterator<Item = CStatement> {
        bytes.map(move |(offset, mask)| CStatement::Store {
            pointer: self.byte_address(offset),
            value: value_at(offset),
            value_type: Some(InterfaceType::UInt8),
            lvalue_class: Some(crate::kernel::effective_type::CAccessClass::BitFieldByte(
                mask,
            )),
            pointee_constant: self.read_only,
            site: CSite::NONE,
        })
    }

    fn copy_from(&self, source: &LocalBitFields) -> CStatement {
        CStatement::AggregateCopy {
            target: self.address(),
            source: source.address(),
            layout: self.record.storage.clone(),
            site: CSite::NONE,
        }
    }

    pub(super) fn member_operator(&self) -> Token {
        if self.pointer.is_some() {
            Token::Arrow
        } else {
            Token::Dot
        }
    }
}

impl Slice {
    fn byte_masks(self) -> impl Iterator<Item = (u32, NonZeroU8)> {
        self.placement.byte_masks().map(|(offset, mask)| {
            (
                u32::try_from(offset).expect("byte offset validated with record size"),
                NonZeroU8::new(mask).expect("byte intersects the field"),
            )
        })
    }

    fn promote(self, bits: CExpression) -> CExpression {
        let width = self.placement.width();
        if !self.signed && width == 32 {
            return bits;
        }
        let value = scalar_cast(bits, InterfaceType::Int32);
        if !self.signed || width == 32 {
            return value;
        }
        // Toggling the sign bit and subtracting its weight extends the x86-64
        // signed field into int without overflowing signed arithmetic.
        let sign = CExpression::Int32Literal(1 << (width - 1));
        let biased = CExpression::BitwiseXor(Box::new(value), Box::new(sign.clone()));
        CExpression::Subtract(Box::new(biased), Box::new(sign))
    }
}

enum RecordInitializer {
    Unwritten,
    Literal {
        bytes: BTreeMap<u32, u8>,
        scalars: BTreeMap<usize, CExpression>,
    },
    Copy(LocalBitFields),
}

fn scalar_cast(expression: CExpression, interface_type: InterfaceType) -> CExpression {
    CExpression::Cast {
        expression: Box::new(expression),
        interface_type,
        struct_name: None,
        pointee_volatile: false,
        pointee_constant: false,
        explicit_qualification: false,
    }
}

fn scalar_declaration(
    name: BindingName,
    interface_type: InterfaceType,
    initializer: Option<CExpression>,
) -> CStatement {
    CStatement::Declare {
        interface_type,
        name: name.into(),
        volatile: false,
        pointee_volatile: false,
        constant: false,
        pointee_constant: false,
        initializer,
        zero_fill: None,
        declared_class: None,
        site: CSite::NONE,
    }
}

impl Parser {
    pub(super) fn parse_int_bit_field(
        &mut self,
        field_type: &ParsedType,
        cursor: &mut u64,
    ) -> Result<Option<(String, Slice)>, CSyntaxError> {
        if !matches!(
            field_type.interface_type,
            InterfaceType::Int32 | InterfaceType::UInt32
        ) || field_type.is_constant
            || field_type.is_volatile
            || field_type.enum_name.is_some()
            || field_type.struct_name.is_some()
            || field_type.union_name.is_some()
            || field_type.aligned_typedef
            || field_type.opaque_builtin
            || field_type.long_double
        {
            return Err(self.error_here(
                "this bit-field layout requires unqualified signed or unsigned int members",
            ));
        }
        let name = if self.peek() == Some(&Token::Colon) {
            None
        } else {
            Some(self.expect_ident("bit-field name")?)
        };
        self.expect(Token::Colon)?;
        let Some(Token::Number(width)) = self.next() else {
            return Err(self.error_at_previous("bit-field width must be a decimal integer literal"));
        };
        let Ok(width @ 0..=32) = width.parse::<u8>() else {
            return Err(self.error_at_previous("bit-field width must be between 0 and 32"));
        };
        let overflow = || self.error_at_previous("bit-field record layout is too large");
        if width == 0 {
            if name.is_some() {
                return Err(self.error_at_previous("a zero-width bit-field must be unnamed"));
            }
            *cursor = IntBitField::next_word(*cursor).ok_or_else(overflow)?;
            return Ok(None);
        }
        let placement = IntBitField::place(*cursor, width).ok_or_else(overflow)?;
        *cursor = placement.end_bit();
        Ok(name.map(|name| {
            (
                name,
                Slice {
                    placement,
                    signed: field_type.interface_type == InterfaceType::Int32,
                },
            )
        }))
    }

    pub(super) fn register_bit_field_record(
        &mut self,
        tag: String,
        mut storage: RecordLayout,
        bit_fields: Vec<(String, Slice)>,
        qualified_scalar: bool,
    ) -> Result<(), CSyntaxError> {
        let mut members: Vec<(u32, NonZeroU8)> = Vec::new();
        for (offset, bits) in bit_fields.iter().flat_map(|(_, field)| field.byte_masks()) {
            if let Some((previous, mask)) = members.last_mut()
                && *previous == offset
            {
                *mask |= bits;
            } else {
                members.push((offset, bits));
            }
        }
        let mut ordered: Vec<_> = bit_fields
            .into_iter()
            .map(|(name, field)| (name, Member::Bits(field)))
            .collect();
        let supports_local_objects = !qualified_scalar
            && storage.fields.values().all(|field| {
                is_arithmetic_type(field.interface_type)
                    && field.enum_name.is_none()
                    && field.struct_name.is_none()
                    && field.union_name.is_none()
                    && !field.long_double
            });
        for (name, field) in &storage.fields {
            ordered.push((
                name.clone(),
                Member::Scalar {
                    offset: field.offset_bytes,
                    width: field.byte_width,
                    ty: field.interface_type,
                },
            ));
        }
        ordered.sort_unstable_by_key(|(_, member)| member.start_bit());
        let mut names = BTreeMap::new();
        let mut fields = Vec::with_capacity(ordered.len());
        for (name, member) in ordered {
            if names.insert(name.clone(), fields.len()).is_some() {
                return Err(self.error_here(format!("duplicate field `{name}` in struct `{tag}`")));
            }
            fields.push(member);
        }
        storage.bit_field_bytes = Some(members.into());
        self.bit_field_records.insert(
            tag,
            Arc::new(BitFieldRecord {
                names,
                fields,
                storage,
                supports_local_objects,
            }),
        );
        Ok(())
    }

    pub(super) fn parse_local_bit_field_record(
        &mut self,
        parsed: &ParsedType,
    ) -> Result<CStatement, CSyntaxError> {
        if self.function_has_goto {
            return Err(
                self.error_here("bit-field objects and goto in one function are not supported")
            );
        }
        self.function_has_bit_fields = true;
        let record =
            self.bit_field_records[parsed.struct_name.as_ref().expect("bit-field tag")].clone();
        if !record.supports_local_objects {
            return Err(self.error_here(
                "local bit-field objects require modeled unqualified arithmetic scalar members",
            ));
        }
        if parsed.volatile_levels != 0 || parsed.aligned_typedef {
            return Err(self.error_here("volatile or aligned bit-field records are not supported"));
        }
        if parsed.pointer_depth == 1 && parsed.interface_type.is_object_pointer() {
            return self.parse_local_bit_field_pointer(parsed, &record);
        }
        if !is_plain_struct_type(parsed) || parsed.is_constant {
            return Err(self.error_here(
                "bit-field objects require a mutable local record or a fixed local pointer to one",
            ));
        }
        let name = self.expect_ident("local bit-field object name")?;
        let binding = self.declare_name(&name)?;
        let initializer = if self.peek() != Some(&Token::Equal) {
            RecordInitializer::Unwritten
        } else {
            self.position += 1;
            if self.peek() == Some(&Token::LBrace) {
                self.parse_bit_field_initializer(&record)?
            } else {
                RecordInitializer::Copy(self.parse_bit_field_copy_source(&record)?)
            }
        };
        self.expect(Token::Semicolon)?;
        self.reserve_bit_field_carrier_ordinal();
        let object = LocalBitFields {
            record,
            storage: binding.clone(),
            pointer: None,
            read_only: false,
        };
        let declaration = CStatement::DeclareStructValue {
            name: object.storage.clone().into(),
            layout: object.record.storage.clone(),
            site: CSite::NONE,
        };
        let mut statements = vec![declaration];
        match initializer {
            RecordInitializer::Unwritten => {}
            RecordInitializer::Literal { bytes, mut scalars } => {
                let members = object
                    .record
                    .storage
                    .bit_field_bytes
                    .as_deref()
                    .expect("bit-field layout");
                statements.extend(object.store_bytes(members.iter().copied(), |offset| {
                    CExpression::UInt8Literal(bytes.get(&offset).copied().unwrap_or(0))
                }));
                for (index, member) in object.record.fields.iter().enumerate() {
                    if let Member::Scalar { offset, ty, width } = *member {
                        let value = scalars
                            .remove(&index)
                            .unwrap_or_else(|| zero_initializer_value(ty));
                        statements.push(object.scalar_store(offset, ty, width, value));
                    }
                }
            }
            RecordInitializer::Copy(source) => statements.push(object.copy_from(&source)),
        }
        self.variable_types
            .insert(binding.clone(), record_value_type(&object.record.storage));
        self.local_bit_fields.insert(binding, object);
        Ok(balanced_statement_sequence(statements).expect("bit-field object declaration"))
    }

    fn parse_local_bit_field_pointer(
        &mut self,
        parsed: &ParsedType,
        record: &Arc<BitFieldRecord>,
    ) -> Result<CStatement, CSyntaxError> {
        let name = self.expect_ident("local bit-field pointer name")?;
        let binding = self.declare_name(&name)?;
        if self.peek() != Some(&Token::Equal) || self.peek_next() != Some(&Token::Amp) {
            return Err(self.error_here(
                "a bit-field pointer must be initialized with the address of a named local record",
            ));
        }
        self.position += 2;
        let mut object = self.parse_bit_field_copy_source(record)?;
        if object.pointer.is_some() {
            return Err(
                self.error_here("a bit-field pointer requires a directly named local target")
            );
        }
        self.expect(Token::Semicolon)?;
        let address = scalar_cast(object.address(), InterfaceType::UInt32Pointer);
        self.reserve_bit_field_carrier_ordinal();
        object.pointer = Some(binding.clone());
        object.read_only = parsed.pointee_constant;
        self.variable_types
            .insert(binding.clone(), parsed.interface_type);
        self.local_bit_fields.insert(binding.clone(), object);
        Ok(scalar_declaration(
            binding,
            InterfaceType::UInt32Pointer,
            Some(address),
        ))
    }

    /// Parse one same-type local record, either named or reached through a
    /// fixed local pointer. The enclosing operation checks its delimiter.
    fn parse_bit_field_copy_source(
        &mut self,
        record: &Arc<BitFieldRecord>,
    ) -> Result<LocalBitFields, CSyntaxError> {
        let dereference = self.peek() == Some(&Token::Star);
        self.position += usize::from(dereference);
        let Some(source) = self.local_bit_field_object().cloned() else {
            return Err(self.error_here("a bit-field copy requires a named local record or dereferenced local bit-field pointer"));
        };
        if dereference != source.pointer.is_some() || !Arc::ptr_eq(record, &source.record) {
            return Err(self
                .error_here("bit-field copies and pointer bindings require the same struct type"));
        }
        self.position += 1;
        Ok(source)
    }

    /// Preserve canonical selectors for locals after a former carrier.
    fn reserve_bit_field_carrier_ordinal(&mut self) {
        self.next_local_binding = self
            .next_local_binding
            .checked_add(1)
            .expect("binding ordinal fits u32");
    }

    fn track_bit_field_binding(
        &mut self,
        name: BindingName,
        interface_type: InterfaceType,
    ) -> BindingName {
        self.variable_types.insert(name.clone(), interface_type);
        self.scopes
            .last_mut()
            .expect("local bit-field scope")
            .push(ScopeBinding {
                source_name: None,
                kernel_name: name.clone(),
                shadowed: None,
                previous_visible: None,
            });
        name
    }

    fn parse_bit_field_initializer(
        &mut self,
        record: &BitFieldRecord,
    ) -> Result<RecordInitializer, CSyntaxError> {
        self.expect(Token::LBrace)?;
        let mut bytes = BTreeMap::new();
        let mut scalars = BTreeMap::new();
        let mut index = 0;
        let mut selected = BTreeSet::new();
        loop {
            if self.peek() == Some(&Token::Dot) {
                self.position += 1;
                let field = self.expect_ident("designated bit-field")?;
                index = *record.names.get(&field).ok_or_else(|| {
                    self.error_at_previous(format!("unknown bit-field `{field}`"))
                })?;
                self.expect(Token::Equal)?;
            }
            let field = *record
                .fields
                .get(index)
                .ok_or_else(|| self.error_here("too many bit-field initializers"))?;
            if !selected.insert(index) {
                return Err(self.error_here("repeated bit-field initializers are not supported"));
            }
            let value = self.parse_assignment()?;
            match field {
                Member::Bits(field) => {
                    let value = match value {
                        CExpression::Int32Literal(value) | CExpression::UInt32Literal(value) => {
                            value
                        }
                        _ => {
                            return Err(self.error_here(
                                "bit-field initializers currently require integer literals",
                            ));
                        }
                    };
                    let positioned = (value << field.placement.shift_in_word()).to_le_bytes();
                    for (offset, mask) in field.byte_masks() {
                        *bytes.entry(offset).or_insert(0) |=
                            positioned[(offset % 4) as usize] & mask.get();
                    }
                }
                Member::Scalar { .. } => {
                    if !matches!(
                        value,
                        CExpression::Int32Literal(_)
                            | CExpression::UInt32Literal(_)
                            | CExpression::Int64Literal(_)
                            | CExpression::UInt64Literal(_)
                            | CExpression::UInt8Literal(_)
                            | CExpression::Float32Literal(_)
                            | CExpression::Float64Literal(_)
                    ) {
                        return Err(self.error_here("mixed-record scalar initializers currently require arithmetic literals"));
                    }
                    scalars.insert(index, value);
                }
            }
            index += 1;
            if self.peek() != Some(&Token::Comma) {
                break;
            }
            self.position += 1;
            if self.peek() == Some(&Token::RBrace) {
                break;
            }
        }
        self.expect(Token::RBrace)?;
        Ok(RecordInitializer::Literal { bytes, scalars })
    }

    pub(super) fn local_bit_field_object(&self) -> Option<&LocalBitFields> {
        if self.local_bit_fields.is_empty() {
            return None;
        }
        crate::instrumentation::record_deterministic_work(1);
        let (_, binding) = self.visible_bindings.get(self.peek_ident()?)?;
        self.local_bit_fields.get(binding)
    }

    fn parse_local_bit_field_member(
        &mut self,
        object: &LocalBitFields,
    ) -> Result<Member, CSyntaxError> {
        self.position += 1;
        if self.peek() != Some(&object.member_operator()) {
            return Err(self.error_here("bit-field objects require a direct named member access"));
        }
        self.position += 1;
        let member = self.expect_ident("bit-field name")?;
        let index = object
            .record
            .names
            .get(&member)
            .ok_or_else(|| self.error_at_previous(format!("unknown bit-field `{member}`")))?;
        Ok(object.record.fields[*index])
    }

    pub(super) fn parse_local_bit_field_read(
        &mut self,
        object: LocalBitFields,
    ) -> Result<CExpression, CSyntaxError> {
        let field = self.parse_local_bit_field_member(&object)?;
        if self.bit_field_forbidden_operand && matches!(field, Member::Bits(_)) {
            return Err(self.error_here(
                "bit-field accesses are not supported in address or unevaluated operands",
            ));
        }
        Ok(object.read_member(field))
    }

    pub(super) fn parse_local_bit_field_store(
        &mut self,
    ) -> Result<Option<CStatement>, CSyntaxError> {
        let start = self.position;
        let prefix = match self.peek() {
            Some(Token::PlusPlus | Token::MinusMinus) => self.next(),
            _ => None,
        };
        let dereference = self.peek() == Some(&Token::Star);
        self.position += usize::from(dereference);
        let Some(object) = self.local_bit_field_object().cloned() else {
            self.position = start;
            return Ok(None);
        };
        if prefix.is_none() && self.peek_next() == Some(&Token::Equal) {
            if dereference != object.pointer.is_some() {
                return Err(
                    self.error_here("reassigning a local bit-field pointer is not supported")
                );
            }
            if object.read_only {
                return Err(
                    self.error_here("cannot assign through a pointer to a const bit-field record")
                );
            }
            self.position += 2;
            let source = self.parse_bit_field_copy_source(&object.record)?;
            self.expect(Token::Semicolon)?;
            return Ok(Some(object.copy_from(&source)));
        }
        if dereference || self.peek_next() != Some(&object.member_operator()) {
            self.position = start;
            return Ok(None);
        }
        if prefix.is_none()
            && !matches!(
                self.peek_n(3),
                Some(
                    Token::Equal
                        | Token::PlusPlus
                        | Token::MinusMinus
                        | Token::PlusEqual
                        | Token::MinusEqual
                )
            )
        {
            self.position = start;
            return Ok(None);
        }
        if object.read_only {
            return Err(
                self.error_here("cannot assign through a pointer to a const bit-field record")
            );
        }
        let field = self.parse_local_bit_field_member(&object)?;
        let operator = prefix
            .or_else(|| self.next())
            .expect("checked member operator");
        let rhs = match operator {
            Token::PlusPlus | Token::MinusMinus => CExpression::Int32Literal(1),
            _ => {
                let value = self.parse_expression()?;
                if !self
                    .source_expression_type(&value)
                    .is_some_and(|ty| match field {
                        Member::Bits(_) => is_integer_type(ty),
                        Member::Scalar { .. } => is_arithmetic_type(ty),
                    })
                    || self.expression_has_runtime_effect(&value)
                {
                    return Err(self.error_here(
                        "member assignment requires a side-effect-free expression of the supported arithmetic type",
                    ));
                }
                value
            }
        };
        let value = match operator {
            Token::Equal => rhs,
            Token::PlusPlus | Token::PlusEqual => {
                CExpression::Add(Box::new(object.read_member(field)), Box::new(rhs))
            }
            Token::MinusMinus | Token::MinusEqual => {
                CExpression::Subtract(Box::new(object.read_member(field)), Box::new(rhs))
            }
            _ => unreachable!("bit-field member assignment operator"),
        };
        self.expect(Token::Semicolon)?;
        let field = match field {
            Member::Scalar { offset, ty, width } => {
                return Ok(Some(object.scalar_store(offset, ty, width, value)));
            }
            Member::Bits(field) => field,
        };
        // Save the converted value before writing any byte: a field may
        // span bytes and its RHS may read from the same allocation.
        let owner = self
            .binding_function
            .clone()
            .ok_or_else(|| self.error_here("a bit-field store requires a function body"))?;
        let ordinal = self.next_local_binding;
        self.next_local_binding = ordinal.checked_add(1).expect("binding ordinal fits u32");
        let temporary = self.track_bit_field_binding(
            LocalBindingId::temporary(owner, ordinal)
                .with_scope_depth(self.scopes.len() as u32)
                .into(),
            InterfaceType::UInt32,
        );
        let positioned = CExpression::ShiftLeft(
            Box::new(scalar_cast(value, InterfaceType::UInt32)),
            Box::new(CExpression::Int32Literal(field.placement.shift_in_word())),
        );
        let evaluation =
            scalar_declaration(temporary.clone(), InterfaceType::UInt32, Some(positioned));
        let statements = std::iter::once(evaluation)
            .chain(object.store_bytes(field.byte_masks(), |offset| {
                CExpression::ShiftRight(
                    Box::new(CExpression::Variable(temporary.clone())),
                    Box::new(CExpression::Int32Literal(8 * (offset % 4))),
                )
            }))
            .collect();
        Ok(balanced_statement_sequence(statements))
    }

    pub(super) fn without_bit_field_operands<T>(
        &mut self,
        parse: impl FnOnce(&mut Self) -> Result<T, CSyntaxError>,
    ) -> Result<T, CSyntaxError> {
        let prior = std::mem::replace(&mut self.bit_field_forbidden_operand, true);
        let result = parse(self);
        self.bit_field_forbidden_operand = prior;
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bit_fields_keep_address_and_unevaluated_operand_restrictions() {
        for (access, diagnostic) in [
            (
                "return &f.ready == 0;",
                "bit-field accesses are not supported in address or unevaluated operands",
            ),
            (
                "return sizeof(f.ready);",
                "bit-field accesses are not supported in address or unevaluated operands",
            ),
            (
                "return f;",
                "bit-field objects require a direct named member access",
            ),
            ("goto done; done: return 0;", "bit-field objects and goto"),
        ] {
            let source = format!(
                "struct flags {{ unsigned int ready : 1; }}; int g(void) {{ struct flags f = {{1}}; {access} }}"
            );
            let error =
                super::super::parse_functions(&source).expect_err("unsupported bit-field operand");
            assert!(error.message().contains(diagnostic), "{}", error.message());
        }
    }

    #[test]
    fn typed_local_bit_field_aliases_keep_their_target_and_qualification() {
        for (access, diagnostic) in [
            (
                "struct flags *p = &f; p = &f; return 0;",
                "reassigning a local bit-field pointer",
            ),
            (
                "const struct flags *p = &f; p->ready = 0; return 0;",
                "cannot assign through a pointer to a const bit-field record",
            ),
        ] {
            let source = format!(
                "struct flags {{ unsigned int ready : 1; }}; int g(void) {{ struct flags f = {{1}}; {access} }}"
            );
            let error = super::super::parse_functions(&source)
                .expect_err("a fixed bit-field alias cannot change target or write through const");
            assert!(error.message().contains(diagnostic), "{}", error.message());
        }
    }

    mod scaling_tests {
        include!("../../../scaling_tests/languages/c/syntax/bit_fields.rs");
    }
}
