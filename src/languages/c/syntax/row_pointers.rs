//! Fixed-width pointers into local two-dimensional scalar arrays.
use super::*;

#[derive(Clone)]
pub(super) struct LocalRowPointer {
    pub(super) storage: BindingName,
    element_type: InterfaceType,
    columns: u32,
}

impl Parser {
    pub(super) fn starts_local_row_pointer_declarator(&self) -> bool {
        self.peek() == Some(&Token::LParen)
            && self.peek_n(1) == Some(&Token::Star)
            && matches!(self.peek_n(2), Some(Token::Ident(_)))
            && self.peek_n(3) == Some(&Token::RParen)
            && self.peek_n(4) == Some(&Token::LBracket)
    }

    pub(super) fn parse_local_row_pointer(
        &mut self,
        parsed_type: &ParsedType,
    ) -> Result<CStatement, CSyntaxError> {
        let element_type = parsed_type.interface_type;
        if !is_arithmetic_type(element_type)
            || parsed_type.struct_name.is_some()
            || parsed_type.enum_name.is_some()
            || parsed_type.union_name.is_some()
            || parsed_type.is_constant
            || parsed_type.is_volatile
            || parsed_type.aligned_typedef
            || parsed_type.long_double
            || parsed_type.opaque_builtin
        {
            return Err(self.error_here(
                "local row pointers require unqualified, modeled arithmetic elements",
            ));
        }

        self.expect(Token::LParen)?;
        self.expect(Token::Star)?;
        let source_name = self.expect_ident("row pointer name")?;
        let name = self.declare_name(&source_name)?;
        self.expect(Token::RParen)?;
        let (array_type, dimensions, incomplete) = self.parse_local_array_shape(parsed_type)?;
        if dimensions.is_some() || incomplete {
            return Err(self.error_here("a row pointer requires one explicit row bound"));
        }
        let columns = array_type.array_length().expect("a fixed row is an array");
        let interface_type = element_type
            .pointer_type()
            .expect("an array element has a pointer type");
        self.expect(Token::Equal)?;

        // The carrier has no C source spelling. The frontend checks every
        // use before lowering it to scalar-pointer operations on the carrier.
        let storage = self.new_automatic_binding(
            self.binding_function
                .is_none()
                .then(|| format!("__click_row_pointer_{source_name}")),
        );
        let row = LocalRowPointer {
            storage: storage.clone(),
            element_type,
            columns,
        };
        let initializer = self.parse_row_pointer_value(&row)?;
        self.expect(Token::Semicolon)?;
        self.variable_types.insert(name.clone(), interface_type);
        self.variable_types.insert(storage.clone(), interface_type);
        self.local_row_pointers.insert(name, row);
        Ok(CStatement::Declare {
            name: storage.into(),
            interface_type,
            volatile: false,
            pointee_volatile: false,
            constant: false,
            pointee_constant: false,
            initializer: Some(initializer),
            zero_fill: None,
            declared_class: None,
            site: CSite::NONE,
        })
    }

    fn parse_row_pointer_value(
        &mut self,
        row: &LocalRowPointer,
    ) -> Result<CExpression, CSyntaxError> {
        let address_of_row = self.peek() == Some(&Token::Amp);
        if address_of_row {
            self.position += 1;
        }
        let source_name = self.expect_ident("local matrix or row pointer")?;
        let name = self.resolve_name(&source_name);
        let base = if let Some(source) = self.local_row_pointers.get(&name) {
            if address_of_row
                || source.columns != row.columns
                || source.element_type != row.element_type
            {
                return Err(
                    self.error_here("incompatible local row pointer initializer or assignment")
                );
            }
            CExpression::Variable(source.storage.clone())
        } else {
            let compatible_matrix = name.local_id().is_some()
                && !self.variable_is_constant(&name)
                && !self.variable_structs.contains_key(&name)
                && self
                    .variable_array_shapes
                    .get(&name)
                    .is_some_and(|shape| shape.len() == 2 && shape[1] == row.columns);
            let matrix_type = self
                .variable_types
                .get(&name)
                .copied()
                .filter(|ty| {
                    compatible_matrix
                        && ty.array_length().is_some()
                        && ty.pointee_type() == Some(row.element_type)
                })
                .ok_or_else(|| {
                    self.error_here("row pointer requires a compatible local two-dimensional array")
                })?;
            CExpression::Subobject {
                pointer: Box::new(CExpression::Variable(name)),
                width: matrix_type.abi_size_bytes(),
            }
        };
        let base = if address_of_row {
            let index = self.parse_row_subscript()?;
            self.offset_row_pointer(base, index, row.columns, false)?
        } else {
            base
        };
        if matches!(self.peek(), Some(Token::Plus | Token::Minus)) {
            let subtract = self.next() == Some(Token::Minus);
            let delta = self.parse_multiply()?;
            return self.offset_row_pointer(base, delta, row.columns, subtract);
        }
        Ok(base)
    }

    pub(super) fn parse_row_pointer_access(
        &mut self,
        row: &LocalRowPointer,
    ) -> Result<CExpression, CSyntaxError> {
        if self.peek() != Some(&Token::LBracket) {
            return Err(self.error_here("use a local row pointer with two subscripts or in a row pointer declaration or update"));
        }
        let index = self.parse_row_subscript()?;
        let base = self.offset_row_pointer(
            CExpression::Variable(row.storage.clone()),
            index,
            row.columns,
            false,
        )?;
        if self.peek() != Some(&Token::LBracket) {
            return Err(self.error_here("a row pointer element access requires two subscripts"));
        }
        let column = self.parse_row_subscript()?;
        let pointer = CExpression::Subobject {
            pointer: Box::new(base),
            width: row.columns * row.element_type.abi_size_bytes(),
        };
        Ok(self.index_expression(pointer, column))
    }

    pub(super) fn parse_row_pointer_update(
        &mut self,
        row: &LocalRowPointer,
        operator: Token,
    ) -> Result<CStatement, CSyntaxError> {
        let expression = match operator {
            Token::Equal => self.parse_row_pointer_value(row)?,
            Token::PlusPlus | Token::MinusMinus | Token::PlusEqual | Token::MinusEqual => {
                let delta = if matches!(operator, Token::PlusPlus | Token::MinusMinus) {
                    CExpression::Int32Literal(1)
                } else {
                    self.parse_expression()?
                };
                self.offset_row_pointer(
                    CExpression::Variable(row.storage.clone()),
                    delta,
                    row.columns,
                    matches!(operator, Token::MinusMinus | Token::MinusEqual),
                )?
            }
            _ => return Err(self.error_here("local row pointers support only assignment, increment, decrement, and additive updates")),
        };
        Ok(CStatement::Assign {
            name: row.storage.clone(),
            expression,
            prior_result: None,
            site: CSite::NONE,
        })
    }

    fn parse_row_subscript(&mut self) -> Result<CExpression, CSyntaxError> {
        self.expect(Token::LBracket)?;
        let index = self.parse_expression()?;
        self.expect(Token::RBracket)?;
        Ok(index)
    }

    fn offset_row_pointer(
        &self,
        pointer: CExpression,
        index: CExpression,
        columns: u32,
        subtract: bool,
    ) -> Result<CExpression, CSyntaxError> {
        if !self
            .source_expression_type(&index)
            .is_some_and(|ty| is_integer_type(ty) && ty.abi_size_bytes() <= 4)
        {
            return Err(
                self.error_here("row pointer offsets require a modeled integer of at most 32 bits")
            );
        }
        crate::instrumentation::record_deterministic_work(1);
        let pointer = Box::new(pointer);
        let index = Box::new(widened_stride(index, columns));
        Ok(if subtract {
            CExpression::Subtract(pointer, index)
        } else {
            CExpression::Add(pointer, index)
        })
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/languages/c/syntax/row_pointers.rs");
}
