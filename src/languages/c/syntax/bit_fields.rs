//! Named int bit-fields in automatic records and fixed local pointers to them.
use super::bit_field_layout::IntBitField;
use super::*;
use std::sync::Arc;

/// One physical slice of the struct's unsigned allocation word.
#[derive(Clone, Copy, Debug)]
struct Slice {
    shift: u32,
    mask: u32,
    signed: bool,
}

#[derive(Debug)]
pub(super) struct BitFieldRecord {
    names: BTreeMap<String, usize>,
    fields: Vec<Slice>,
    storage: RecordLayout,
    complete_mask: u32,
}

impl BitFieldRecord {
    pub(super) fn size_bytes(&self) -> u32 {
        self.storage.size_bytes
    }
}

#[derive(Clone, Debug)]
pub(super) struct LocalBitFields {
    record: Arc<BitFieldRecord>,
    word: BindingName,
    /// A runtime binding is retained even though its pointee is fixed by
    /// syntax. Reading it still checks that C executed its initializer.
    pointer: Option<BindingName>,
    read_only: bool,
}

impl LocalBitFields {
    fn address(&self) -> CExpression {
        match &self.pointer {
            Some(pointer) => CExpression::Variable(pointer.clone()),
            None => CExpression::AddressOf(Box::new(CExpression::Variable(self.word.clone()))),
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

    fn read(&self, field: Slice) -> CExpression {
        let mut selected = None;
        for (offset, mask) in byte_slices(field.mask) {
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
                Box::new(CExpression::Int32Literal(8 * offset)),
            );
            selected = Some(match selected {
                None => positioned,
                Some(previous) => CExpression::BitwiseOr(Box::new(previous), Box::new(positioned)),
            });
        }
        let shifted = CExpression::ShiftRight(
            Box::new(selected.expect("nonempty field")),
            Box::new(CExpression::Int32Literal(field.shift)),
        );
        field.promote(shifted)
    }

    fn store_bytes(
        &self,
        mask: u32,
        mut value_at: impl FnMut(u32) -> CExpression,
    ) -> impl Iterator<Item = CStatement> {
        byte_slices(mask).map(move |(offset, mask)| CStatement::Store {
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

fn byte_slices(mask: u32) -> impl Iterator<Item = (u32, std::num::NonZeroU8)> {
    mask.to_le_bytes()
        .into_iter()
        .enumerate()
        .filter_map(|(offset, mask)| Some((offset as u32, std::num::NonZeroU8::new(mask)?)))
}

impl Slice {
    fn promote(self, bits: CExpression) -> CExpression {
        let width = self.mask.count_ones();
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
    Literal(u32),
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
    pub(super) fn parse_bit_field_record(
        &mut self,
        tag: String,
        mut field_type: ParsedType,
    ) -> Result<(), CSyntaxError> {
        if self.current_function_source_name.is_some() {
            return Err(
                self.error_here("bit-field record definitions currently require file scope")
            );
        }
        let mut names = BTreeMap::new();
        let mut fields = Vec::new();
        let mut cursor = 0;
        let mut complete_mask = 0;
        loop {
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
            let signed = field_type.interface_type == InterfaceType::Int32;
            loop {
                let name = self.expect_ident("bit-field name")?;
                self.expect(Token::Colon)?;
                let Some(Token::Number(width)) = self.next() else {
                    return Err(
                        self.error_at_previous("bit-field width must be a decimal integer literal")
                    );
                };
                let placement = width
                    .parse::<u8>()
                    .ok()
                    .and_then(|width| IntBitField::place(cursor, width));
                let Some(placement) = placement else {
                    return Err(self.error_at_previous("bit-field width must be between 1 and 32"));
                };
                let Some((shift, mask)) = placement.first_word_slice() else {
                    return Err(
                        self.error_at_previous("bit-fields must fit in one 32-bit allocation word")
                    );
                };
                if names.insert(name.clone(), fields.len()).is_some() {
                    return Err(self.error_at_previous(format!("duplicate bit-field `{name}`")));
                }
                fields.push(Slice {
                    shift,
                    mask,
                    signed,
                });
                complete_mask |= mask;
                cursor = placement.end_bit();
                if self.peek() != Some(&Token::Comma) {
                    break;
                }
                self.position += 1;
            }
            self.expect(Token::Semicolon)?;
            if self.peek() == Some(&Token::RBrace) {
                break;
            }
            field_type = self.parse_type()?;
        }
        self.expect(Token::RBrace)?;
        if self.consume_struct_alignment_attribute()?.is_some() {
            return Err(self.error_at_previous("aligned bit-field records are not supported"));
        }
        if self.structs.contains_key(&tag) || self.bit_field_records.contains_key(&tag) {
            return Err(self.error_at_previous(format!("duplicate struct declaration `{tag}`")));
        }
        // The layout defines the allocation. The bit-field registry alone
        // describes C members, so ordinary aggregate lowering cannot treat
        // these slices as separately addressable cells.
        let mut storage =
            RecordLayout::from_explicit_fields_with_structs(Vec::new(), 4, 4, &BTreeMap::new())
                .expect("one aligned allocation word");
        storage.bit_field_bits = std::num::NonZeroU32::new(complete_mask);
        storage.class = Some(
            crate::kernel::effective_type::CStructContentsBuilder::default().build(tag.clone()),
        );
        self.bit_field_records.insert(
            tag,
            Arc::new(BitFieldRecord {
                names,
                fields,
                storage,
                complete_mask,
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
                RecordInitializer::Literal(self.parse_bit_field_initializer(&record)?)
            } else {
                RecordInitializer::Copy(self.parse_bit_field_copy_source(&record)?)
            }
        };
        self.expect(Token::Semicolon)?;
        let word = self.hidden_bit_field_binding("word", record_value_type(&record.storage));
        let object = LocalBitFields {
            record,
            word,
            pointer: None,
            read_only: false,
        };
        let declaration = CStatement::DeclareStructValue {
            name: object.word.clone().into(),
            layout: object.record.storage.clone(),
            site: CSite::NONE,
        };
        let mut statements = vec![declaration];
        match initializer {
            RecordInitializer::Unwritten => {}
            RecordInitializer::Literal(value) => {
                let bytes = value.to_le_bytes();
                statements.extend(object.store_bytes(object.record.complete_mask, |offset| {
                    CExpression::UInt8Literal(bytes[offset as usize])
                }));
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
        let pointer = self.hidden_bit_field_binding("pointer", InterfaceType::UInt32Pointer);
        object.pointer = Some(pointer.clone());
        object.read_only = parsed.pointee_constant;
        self.variable_types
            .insert(binding.clone(), parsed.interface_type);
        self.local_bit_fields.insert(binding, object);
        Ok(scalar_declaration(
            pointer,
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

    fn hidden_bit_field_binding(
        &mut self,
        purpose: &str,
        interface_type: InterfaceType,
    ) -> BindingName {
        let name = self.new_automatic_binding(Some(format!(
            "__click_bit_field_{purpose}_{}",
            self.next_local_binding
        )));
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
    ) -> Result<u32, CSyntaxError> {
        self.expect(Token::LBrace)?;
        let mut word = 0;
        let mut index = 0;
        let mut selected = 0;
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
            if selected & field.mask != 0 {
                return Err(self.error_here("repeated bit-field initializers are not supported"));
            }
            let value = self.parse_assignment()?;
            let value = match value {
                CExpression::Int32Literal(value) | CExpression::UInt32Literal(value) => value,
                _ => {
                    return Err(self
                        .error_here("bit-field initializers currently require integer literals"));
                }
            };
            word |= (value << field.shift) & field.mask;
            selected |= field.mask;
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
        Ok(word)
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
    ) -> Result<Slice, CSyntaxError> {
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
        if self.bit_field_forbidden_operand {
            return Err(self.error_here(
                "bit-field accesses are not supported in address or unevaluated operands",
            ));
        }
        let field = self.parse_local_bit_field_member(&object)?;
        Ok(object.read(field))
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
                    .is_some_and(is_integer_type)
                    || self.expression_has_runtime_effect(&value)
                {
                    return Err(self.error_here(
                        "bit-field assignment requires a side-effect-free integer expression",
                    ));
                }
                value
            }
        };
        let value = match operator {
            Token::Equal => rhs,
            Token::PlusPlus | Token::PlusEqual => {
                CExpression::Add(Box::new(object.read(field)), Box::new(rhs))
            }
            Token::MinusMinus | Token::MinusEqual => {
                CExpression::Subtract(Box::new(object.read(field)), Box::new(rhs))
            }
            _ => unreachable!("bit-field member assignment operator"),
        };
        self.expect(Token::Semicolon)?;
        // Save the converted value before writing any byte: a field may
        // span bytes and its RHS may read from the same allocation.
        let temporary = self.hidden_bit_field_binding("value", InterfaceType::UInt32);
        let positioned = CExpression::ShiftLeft(
            Box::new(scalar_cast(value, InterfaceType::UInt32)),
            Box::new(CExpression::Int32Literal(field.shift)),
        );
        let evaluation =
            scalar_declaration(temporary.clone(), InterfaceType::UInt32, Some(positioned));
        let statements = std::iter::once(evaluation)
            .chain(object.store_bytes(field.mask, |offset| {
                CExpression::ShiftRight(
                    Box::new(CExpression::Variable(temporary.clone())),
                    Box::new(CExpression::Int32Literal(8 * offset)),
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
