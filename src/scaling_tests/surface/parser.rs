use super::*;

/// The tokens `looks_like_algebraic_constructor` examines while `source`
/// parses, without the standard library.
fn constructor_lookahead_tokens(source: &str) -> usize {
    CONSTRUCTOR_LOOKAHEAD_TOKENS.with(|count| count.set(0));
    parse_file_items(source).unwrap_or_else(|error| panic!("{source}: {}", error.message()));
    CONSTRUCTOR_LOOKAHEAD_TOKENS.with(std::cell::Cell::get)
}

/// Each sample doubles the input size.
fn assert_linear(samples: &[usize]) {
    for pair in samples.windows(2) {
        assert!(
            pair[1] <= pair[0].saturating_mul(2).saturating_add(16),
            "{samples:?}"
        );
    }
}

#[test]
fn comparison_lookahead_stops_at_its_proposition() {
    // Each `x < y` once scanned to the end of the file for a `>` followed by
    // `::`, so a file of comparisons parsed in quadratic time. A conjunction
    // stays under the parser's 512-operator nesting limit.
    let statements = [32, 64, 128, 256].map(|size| {
        let mut source = String::from("theorem many(x: Integer, y: Integer) {\n");
        for _ in 0..size {
            source.push_str("    requires x < y;\n");
        }
        source.push_str("    ensures x < y by { known(); }\n}\n");
        constructor_lookahead_tokens(&source)
    });
    assert_linear(&statements);
    let conjuncts = [32, 64, 128, 256].map(|size| {
        let chain = vec!["x < y"; size].join(" and ");
        let source = format!(
            "theorem chain(x: Integer, y: Integer) {{\n    requires {chain};\n    ensures x < y by {{ known(); }}\n}}\n"
        );
        constructor_lookahead_tokens(&source)
    });
    assert_linear(&conjuncts);
}

#[test]
fn literal_reference_parsing_shares_the_source_index_as_other_literals_grow() {
    let mut samples = Vec::new();
    for count in [1, 16, 256] {
        let mut layouts = ProgramLayouts::default();
        for ordinal in 0..count {
            let id = crate::kernel::StringLiteralId::new("f", ordinal);
            let pointer = crate::kernel::Memory::string_literal_pointer(&id, b"x\0");
            std::sync::Arc::make_mut(&mut layouts.string_literal_values).insert(
                id,
                ProgramValue::typed_pointer(pointer, ProgramType::UInt8Pointer),
            );
        }
        std::sync::Arc::make_mut(&mut layouts.string_literal_owners)
            .insert("f".into(), BTreeSet::from([None]));
        let index = layouts.string_literal_values.clone();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut parser =
                Parser::with_program_layouts("f.string_literal(0)", layouts, None).unwrap();
            assert!(std::sync::Arc::ptr_eq(
                &index,
                &parser.string_literal_values
            ));
            parser.parse_contract_expression().unwrap()
        });
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 64),
        "{samples:?}"
    );
}

#[test]
fn static_declaration_preparation_is_linear_and_selector_lookup_is_indexed() {
    for size in [1usize, 16, 256] {
        let mut source = String::new();
        for i in 0..size {
            source.push_str(&format!("static int32 global_{i} = {i};\n"));
        }
        for i in 0..size {
            source.push_str(&format!(
                "int32 function_{i}(void) {{ static int32 local = {i}; return local; }}\n"
            ));
        }
        let unit = syntax::parse_translation_unit_for_source(
            &source,
            "statics.c",
            &crate::languages::c::source::ExpandedLineMap::empty(),
        )
        .unwrap();
        let (layouts, preparation) = crate::instrumentation::measure_deterministic_work(|| {
            let mut layouts = ProgramLayouts::default();
            layouts.register_file_static_bindings(&unit);
            for function in &unit.functions {
                layouts.register_local_bindings(function);
            }
            layouts
        });
        assert!(
            preparation >= 2 * size && preparation <= 6 * size + 8,
            "{size}: {preparation}"
        );
        let (expression, lookup) = crate::instrumentation::measure_deterministic_work(|| {
            let mut parser = Parser::new("\"statics.c\"::static(0)").unwrap();
            parser.local_bindings = layouts.local_bindings.clone();
            parser.parse_contract_expression().unwrap()
        });
        let ContractExpression::ProgramExpression(ProgramExpression::Variable(
            crate::kernel::BindingName::Static(id),
        )) = expression
        else {
            panic!("static selector");
        };
        assert_eq!(id.spelling(), "global_0");
        assert_eq!(lookup, 9, "selector work changed at size {size}");
    }
}
