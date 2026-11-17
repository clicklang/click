//! Named unsigned bit-fields in an automatic struct that cannot escape.
use super::bit_field_layout::IntBitField;
use super::*;
use std::sync::Arc;

/// One physical slice of the struct's unsigned allocation word.
#[derive(Clone, Copy, Debug)]
struct Slice {
    shift: u32,
    mask: u32,
}

#[derive(Debug)]
pub(super) struct BitFieldRecord {
    names: BTreeMap<String, usize>,
    fields: Vec<Slice>,
    storage: RecordLayout,
}

#[derive(Clone, Debug)]
struct PartialInitialization {
    mask: BindingName,
    unwritten: BindingName,
}

#[derive(Clone, Debug)]
pub(super) struct LocalBitFields {
    record: Arc<BitFieldRecord>,
    word: BindingName,
    partial: Option<PartialInitialization>,
}

impl LocalBitFields {
    fn address(&self) -> CExpression {
        CExpression::AddressOf(Box::new(CExpression::Variable(self.word.clone())))
    }

    fn word(&self) -> CExpression {
        CExpression::Field {
            pointer: Box::new(self.address()),
            field_type: InterfaceType::UInt32,
            pointee_constant: false,
            field_struct_name: None,
            function_pointer_signature: None,
            array_shape: None,
            source: None,
            access_class: InterfaceType::UInt32.access_class(),
        }
    }

    fn store(&self, value: CExpression) -> CStatement {
        CStatement::Store {
            pointer: self.address(),
            value,
            value_type: Some(InterfaceType::UInt32),
            lvalue_class: None,
            pointee_constant: false,
            site: CSite::NONE,
        }
    }

    fn read(&self, field: Slice) -> CExpression {
        let selected = CExpression::BitwiseAnd(
            Box::new(self.word()),
            Box::new(CExpression::UInt32Literal(field.mask)),
        );
        let shifted = CExpression::ShiftRight(
            Box::new(selected),
            Box::new(CExpression::Int32Literal(field.shift)),
        );
        // Every admitted unsigned field is narrower than int. Its promoted
        // value therefore has type int and is representable without overflow.
        let value = scalar_cast(shifted, InterfaceType::Int32);
        let Some(partial) = &self.partial else {
            return value;
        };
        let written = CExpression::BitwiseAnd(
            Box::new(CExpression::Variable(partial.mask.clone())),
            Box::new(CExpression::UInt32Literal(field.mask)),
        );
        CExpression::Ternary {
            condition: Box::new(CExpression::Equal(
                Box::new(written),
                Box::new(CExpression::UInt32Literal(field.mask)),
            )),
            then_branch: Box::new(value),
            else_branch: Box::new(CExpression::Variable(partial.unwritten.clone())),
        }
    }

    fn update(&self, field: Slice, value: CExpression) -> CStatement {
        let preserved = CExpression::BitwiseAnd(
            Box::new(self.word()),
            Box::new(CExpression::UInt32Literal(!field.mask)),
        );
        let value = CExpression::BitwiseAnd(
            Box::new(scalar_cast(value, InterfaceType::UInt32)),
            Box::new(CExpression::UInt32Literal(field.mask >> field.shift)),
        );
        let inserted = CExpression::ShiftLeft(
            Box::new(value),
            Box::new(CExpression::Int32Literal(field.shift)),
        );
        let store = self.store(CExpression::BitwiseOr(
            Box::new(preserved),
            Box::new(inserted),
        ));
        let Some(partial) = &self.partial else {
            return store;
        };
        CStatement::Seq(
            Box::new(store),
            Box::new(CStatement::Assign {
                name: partial.mask.clone(),
                expression: CExpression::BitwiseOr(
                    Box::new(CExpression::Variable(partial.mask.clone())),
                    Box::new(CExpression::UInt32Literal(field.mask)),
                ),
                site: CSite::NONE,
                prior_result: None,
            }),
        )
    }
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
        loop {
            if field_type.interface_type != InterfaceType::UInt32
                || field_type.is_constant
                || field_type.is_volatile
                || field_type.enum_name.is_some()
                || field_type.aligned_typedef
            {
                return Err(self.error_here(
                    "this bit-field layout requires unqualified unsigned int members",
                ));
            }
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
                    return Err(self.error_at_previous("bit-field width must be between 1 and 31"));
                };
                let Some((shift, mask)) = placement.first_word_slice() else {
                    return Err(self.error_at_previous("bit-fields must be narrower than int and fit in one unsigned allocation word"));
                };
                if names.insert(name.clone(), fields.len()).is_some() {
                    return Err(self.error_at_previous(format!("duplicate bit-field `{name}`")));
                }
                fields.push(Slice { shift, mask });
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
        // Keep this layout out of ordinary struct lookup. The allocation has
        // exactly one unsigned cell and the C member names are bit slices,
        // so ordinary struct, pointer, and byte operations must not import it.
        let storage = RecordLayout::from_explicit_fields_with_structs(
            vec![("<bit-field word>".into(), InterfaceType::UInt32, None, 0, 4)],
            4,
            4,
            &BTreeMap::new(),
        )
        .expect("one aligned unsigned word");
        self.bit_field_records.insert(
            tag,
            Arc::new(BitFieldRecord {
                names,
                fields,
                storage,
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
        if !is_plain_struct_type(parsed)
            || parsed.is_constant
            || parsed.is_volatile
            || parsed.aligned_typedef
        {
            return Err(self.error_here(
                "bit-field records require unqualified, directly accessed local objects",
            ));
        }
        let name = self.expect_ident("local bit-field object name")?;
        let binding = self.declare_name(&name)?;
        let initializer = if self.peek() == Some(&Token::Equal) {
            self.position += 1;
            Some(self.parse_bit_field_initializer(&record)?)
        } else {
            None
        };
        self.expect(Token::Semicolon)?;
        let word = self.hidden_bit_field_binding("word", record_value_type(&record.storage));
        let partial = initializer.is_none().then(|| PartialInitialization {
            mask: self.hidden_bit_field_binding("written", InterfaceType::UInt32),
            unwritten: self.hidden_bit_field_binding("unwritten", InterfaceType::Int32),
        });
        // The private backing word can carry zero for bits C has not written.
        // Those bits cannot be observed: all projections test their written
        // mask, and the source object cannot be addressed or used by value.
        let object = LocalBitFields {
            record,
            word,
            partial,
        };
        let mut statements = vec![
            CStatement::DeclareStructValue {
                name: object.word.clone().into(),
                layout: object.record.storage.clone(),
                site: CSite::NONE,
            },
            object.store(CExpression::UInt32Literal(initializer.unwrap_or(0))),
        ];
        if let Some(partial) = &object.partial {
            statements.push(scalar_declaration(
                partial.mask.clone(),
                InterfaceType::UInt32,
                Some(CExpression::UInt32Literal(0)),
            ));
            statements.push(scalar_declaration(
                partial.unwritten.clone(),
                InterfaceType::Int32,
                None,
            ));
        }
        self.variable_types
            .insert(binding.clone(), record_value_type(&object.record.storage));
        self.local_bit_fields.insert(binding, object);
        Ok(balanced_statement_sequence(statements).expect("bit-field object declaration"))
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
        if self.peek() != Some(&Token::Dot) {
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
        if self.peek_n(1) != Some(&Token::Dot) || self.peek_n(3) != Some(&Token::Equal) {
            return Ok(None);
        }
        let Some(object) = self.local_bit_field_object().cloned() else {
            return Ok(None);
        };
        let field = self.parse_local_bit_field_member(&object)?;
        self.expect(Token::Equal)?;
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
        self.expect(Token::Semicolon)?;
        Ok(Some(object.update(field, value)))
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
    fn local_bit_field_storage_cannot_be_exposed_through_source() {
        for (access, diagnostic) in [
            (
                "return &f == 0;",
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
            let error = super::super::parse_functions(&source)
                .expect_err("bit-field storage cannot escape");
            assert!(error.message().contains(diagnostic), "{}", error.message());
        }
    }

    mod scaling_tests {
        include!("../../../scaling_tests/languages/c/syntax/bit_fields.rs");
    }
}
