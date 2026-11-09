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
        source.push_str("    ensures x < y by { assumption(); }\n}\n");
        constructor_lookahead_tokens(&source)
    });
    assert_linear(&statements);
    let conjuncts = [32, 64, 128, 256].map(|size| {
        let chain = vec!["x < y"; size].join(" and ");
        let source = format!(
            "theorem chain(x: Integer, y: Integer) {{\n    requires {chain};\n    ensures x < y by {{ assumption(); }}\n}}\n"
        );
        constructor_lookahead_tokens(&source)
    });
    assert_linear(&conjuncts);
}
