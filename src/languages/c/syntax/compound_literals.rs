//! Compound literals share named automatic storage and initialization.
use super::*;

impl Parser {
    fn require_compound_literal_scope(&self) -> Result<(), CSyntaxError> {
        if self.function_has_goto {
            return Err(
                self.error_here("compound literals and goto in one function are not supported")
            );
        }
        if self.current_function_source_name.is_none() || self.function_block_depth == 0 {
            return Err(self.error_here("compound literals currently require block scope"));
        }
        Ok(())
    }

    pub(super) fn parse_array_compound_literal(
        &mut self,
        parsed_type: ParsedType,
        bound: Option<u32>,
    ) -> Result<CExpression, CSyntaxError> {
        self.require_compound_literal_scope()?;
        let element_type = parsed_type.interface_type;
        if !is_arithmetic_type(element_type)
            || parsed_type.struct_name.is_some()
            || parsed_type.union_name.is_some()
            || parsed_type.enum_name.is_some()
            || parsed_type.long_double
            || parsed_type.opaque_builtin
        {
            return Err(
                self.error_here("array compound literals require modeled arithmetic elements")
            );
        }
        if parsed_type.is_constant || parsed_type.is_volatile || parsed_type.aligned_typedef {
            return Err(self.error_here(
                "array compound literals require unqualified elements with ordinary alignment",
            ));
        }
        let mut written = Vec::new();
        let mut next = 0;
        let written_count = self.parse_array_initializer_elements(
            "array compound literal",
            bound,
            &[],
            &mut written,
            &mut next,
        )?;
        let length = bound.unwrap_or(written_count);
        if length == 0 || length.checked_mul(element_type.abi_size_bytes()).is_none() {
            return Err(
                self.error_here("array compound literal requires a representable positive bound")
            );
        }
        let interface_type = array_type_for_element(element_type, length)
            .expect("array declarator has a modeled element type");
        let name = self.new_automatic_binding(Some(format!(
            "__click_compound_literal_{}",
            self.next_local_binding
        )));
        let (initializer, initializer_call, initializer_assignment) = if self.unevaluated_operand {
            (CStatement::Skip, None, None)
        } else {
            let (_, mut initializer) = self.finish_local_array_initializer(
                &name,
                element_type,
                written_count,
                written,
                false,
            );
            let (call, assignment) =
                self.validate_compound_literal_initializer_order(&initializer)?;
            if written_count < length {
                initializer = CStatement::Seq(
                    Box::new(initializer),
                    Box::new(CStatement::FillArrayTail {
                        name: name.clone(),
                        element_type,
                        start: written_count,
                        count: length - written_count,
                    }),
                );
            }

            self.function_has_compound_literals = true;
            let declared_class = self.local_declared_class(interface_type, None);
            self.compound_literal_declarations
                .last_mut()
                .expect("literal has a block")
                .push(CStatement::Declare {
                    name: name.clone().into(),
                    interface_type,
                    volatile: false,
                    pointee_volatile: false,
                    constant: false,
                    pointee_constant: false,
                    initializer: None,
                    zero_fill: None,
                    declared_class,
                    site: CSite::NONE,
                });
            (initializer, call, assignment)
        };
        Ok(CExpression::StatementExpression {
            aggregate_lvalue: true,
            initializer_call,
            initializer_assignment,
            scope_lifetimes: Vec::new(),
            body: Box::new(initializer),
            value: Box::new(CExpression::Variable(name)),
            interface_type,
            struct_name: None,
            function_pointer_signature: None,
            pointee_constant: false,
        })
    }

    pub(super) fn parse_struct_compound_literal(
        &mut self,
        parsed_type: ParsedType,
    ) -> Result<CExpression, CSyntaxError> {
        self.require_compound_literal_scope()?;
        let struct_name = parsed_type
            .struct_name
            .as_ref()
            .filter(|_| {
                parsed_type.interface_type == InterfaceType::Int32
                    && parsed_type.pointer_depth == 0
                    && parsed_type.union_name.is_none()
            })
            .ok_or_else(|| {
                self.error_here("compound literals currently require a struct object type")
            })?
            .clone();
        if parsed_type.is_constant {
            return Err(self.error_here("const-qualified struct compound literals require immutable aggregate storage and are not supported"));
        }
        if parsed_type.is_volatile {
            return Err(self.error_here("volatile struct compound literals are not supported"));
        }
        if parsed_type.aligned_typedef {
            return Err(self.error_here("aligned typedef compound literals are not supported"));
        }
        let layout = self.scalar_struct_value_layout(&struct_name)?;
        let name = self.new_automatic_binding(Some(format!(
            "__click_compound_literal_{}",
            self.next_local_binding
        )));
        self.variable_types
            .insert(name.clone(), record_value_type(&layout));
        self.variable_structs
            .insert(name.clone(), struct_name.clone());
        self.variable_struct_values
            .insert(name.clone(), struct_name.clone());
        self.local_struct_values
            .insert(name.clone(), Some(struct_name.clone()));
        self.scopes
            .last_mut()
            .expect("literal has a lexical scope")
            .push(ScopeBinding {
                source_name: None,
                kernel_name: name.clone(),
                shadowed: None,
                previous_visible: None,
            });
        let stores = self.parse_struct_initializer_level(
            CExpression::AddressOf(Box::new(CExpression::Variable(name.clone()))),
            &struct_name,
        )?;
        let initializer = balanced_statement_sequence(stores).unwrap_or(CStatement::Skip);
        let (initializer_call, initializer_assignment) =
            self.validate_compound_literal_initializer_order(&initializer)?;
        self.function_has_compound_literals = true;
        self.compound_literal_declarations
            .last_mut()
            .expect("literal has a block")
            .push(CStatement::DeclareStructValue {
                name: name.clone().into(),
                layout,
                site: CSite::NONE,
            });
        Ok(CExpression::StatementExpression {
            aggregate_lvalue: true,
            initializer_call,
            initializer_assignment,
            scope_lifetimes: Vec::new(),
            body: Box::new(initializer),
            value: Box::new(CExpression::Variable(name)),
            interface_type: InterfaceType::Int32,
            struct_name: Some(struct_name),
            function_pointer_signature: None,
            pointee_constant: false,
        })
    }

    // Initializer-list evaluations are indeterminately sequenced in C. Reuse
    // ordinary field initialization only when its order cannot select between
    // external side effects and another initializer's value. More general lists
    // require explicit alternative evaluation orders, rather than choosing one.
    fn validate_compound_literal_initializer_order(
        &self,
        initializer: &CStatement,
    ) -> Result<(Option<SourcePosition>, Option<SourcePosition>), CSyntaxError> {
        let mut pending = vec![initializer];
        let mut effects = 0;
        let mut other_reads = false;
        let mut call_position = None;
        let mut assignment_position = None;
        while let Some(statement) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            match statement {
                CStatement::Seq(left, right) => {
                    pending.push(right);
                    pending.push(left);
                }
                CStatement::Store { value, .. } => {
                    if self.repeatable_compound_literal_scope == Some(self.scopes.len())
                        && !self.repeatable_compound_literal_value(value)
                    {
                        return Err(self.error_here("repeatable loop-clause compound literal initializers require scalar-local expressions"));
                    }
                    if call_position.is_none() {
                        call_position = first_embedded_call_position(value);
                    }
                    if assignment_position.is_none() {
                        assignment_position = first_assignment_position(value);
                    }
                    if self.expression_has_runtime_effect(value) {
                        effects += 1;
                    } else {
                        other_reads |= expression_reads_runtime_value(value);
                    }
                }
                CStatement::Skip => {}
                _ => unreachable!("aggregate initializer contains element stores"),
            }
        }
        if effects > 1 || (effects != 0 && other_reads) {
            return Err(self.error_here("compound literal initializer evaluations with interacting side effects are not supported"));
        }
        Ok((call_position, assignment_position))
    }

    // Walk only the selected initializer. Physical automatic bindings identify
    // local cells without searching the file's unrelated global declarations.
    fn repeatable_compound_literal_value(&self, mut value: &CExpression) -> bool {
        loop {
            crate::instrumentation::record_deterministic_work(1);
            match value {
                CExpression::Int32Literal(_)
                | CExpression::UInt8Literal(_)
                | CExpression::UInt32Literal(_)
                | CExpression::Int64Literal(_)
                | CExpression::UInt64Literal(_)
                | CExpression::Float32Literal(_)
                | CExpression::Float64Literal(_) => return true,
                CExpression::Variable(name) | CExpression::ScalarUpdate { name, .. } => {
                    return name.local_id().is_some()
                        && self.variable_types.contains_key(name)
                        && !self.variable_struct_values.contains_key(name)
                        && !self.static_locals.contains_key(name);
                }
                CExpression::Cast { expression, .. }
                | CExpression::PointerOffsetBytes {
                    pointer: expression,
                    ..
                }
                | CExpression::Subobject {
                    pointer: expression,
                    ..
                } => value = expression,
                _ => return false,
            }
        }
    }

    /// A literal's initialized place and its fixed subobjects are distinct
    /// from the named scalar cells updated by its initializer. Such updates
    /// are safe for the subsequent member load; their metadata still reaches
    /// enclosing unsequenced operators. A pointer loaded from a member is not
    /// this place and deliberately does not match.
    pub(super) fn compound_literal_storage_address(mut expression: &CExpression) -> bool {
        loop {
            crate::instrumentation::record_deterministic_work(1);
            match expression {
                CExpression::StatementExpression {
                    aggregate_lvalue: true,
                    ..
                } => return true,
                CExpression::AddressOf(inner)
                | CExpression::Cast {
                    expression: inner, ..
                }
                | CExpression::PointerOffsetBytes { pointer: inner, .. }
                | CExpression::Subobject { pointer: inner, .. }
                | CExpression::AggregateAddress { pointer: inner, .. } => expression = inner,
                _ => return false,
            }
        }
    }

    /// Touch only this block's newly introduced objects. Allocation is at block
    /// entry; initialization remains in the expression and can run repeatedly.
    pub(super) fn compound_literal_block_storage(
        &mut self,
        body: CStatement,
    ) -> (CStatement, Vec<BindingName>) {
        let declarations = std::mem::take(
            self.compound_literal_declarations
                .last_mut()
                .expect("open block"),
        );
        let names = declarations
            .iter()
            .map(|declaration| {
                crate::instrumentation::record_deterministic_work(1);
                match declaration {
                    CStatement::DeclareStructValue { name, .. }
                    | CStatement::Declare { name, .. } => name.binding().clone(),
                    _ => unreachable!("literal storage"),
                }
            })
            .collect::<Vec<_>>();
        (prepend_statements(declarations, body), names)
    }

    pub(super) fn finish_compound_literal_block(&mut self, body: CStatement) -> CStatement {
        let (body, names) = self.compound_literal_block_storage(body);
        if names.is_empty() {
            body
        } else {
            CStatement::Seq(
                Box::new(body),
                Box::new(CStatement::EndAggregateLifetimes {
                    names,
                    steps: Vec::new(),
                    site: CSite::NONE,
                }),
            )
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn own_declarations(statement: &CStatement) -> usize {
        let mut pending = vec![statement];
        let mut count = 0;
        while let Some(statement) = pending.pop() {
            match statement {
                CStatement::Seq(left, right) => {
                    pending.push(right);
                    pending.push(left);
                }
                CStatement::DeclareStructValue { .. } => count += 1,
                _ => {}
            }
        }
        count
    }

    #[test]
    fn compound_literal_storage_belongs_to_the_enclosing_block() {
        for (body, declarations_outside) in [
            ("p = &(struct pair){i++, 22};", 0),
            ("{ p = &(struct pair){i++, 22}; }", 0),
        ] {
            let source = format!(
                "struct pair {{ int left; int right; }}; int f(void) {{ int i = 0; struct pair *p = 0; while (i < 2) {body} return i; }}"
            );
            let functions = super::super::parse_functions(&source).unwrap();
            let body = functions[0].body();
            assert_eq!(own_declarations(body), declarations_outside);
            let mut pending = vec![body];
            let mut loop_declarations = None;
            while let Some(statement) = pending.pop() {
                match statement {
                    CStatement::Seq(left, right) => {
                        pending.push(right);
                        pending.push(left);
                    }
                    CStatement::While { body, .. } => {
                        loop_declarations = Some(own_declarations(body))
                    }
                    _ => {}
                }
            }
            assert_eq!(loop_declarations, Some(1 - declarations_outside));
        }
    }

    #[test]
    fn compound_literal_unsupported_storage_and_type_boundaries_are_explicit() {
        for (source, expected) in [
            (
                "int f(void) { int *p = &(int){42}; return *p; }",
                "require a struct object type",
            ),
            (
                "struct pair { int value; }; struct pair *p = &(struct pair){42}; int f(void) { return p->value; }",
                "require block scope",
            ),
            (
                "struct pair { int value; }; int f(void) { const struct pair *p = &(const struct pair){42}; return p->value; }",
                "require immutable aggregate storage",
            ),
        ] {
            let error = super::super::parse_functions(source)
                .expect_err("unmodeled literal type/storage must be refused");
            assert!(error.message().contains(expected), "{}", error.message());
        }
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../../scaling_tests/languages/c/syntax/compound_literals.rs");
    }
}
