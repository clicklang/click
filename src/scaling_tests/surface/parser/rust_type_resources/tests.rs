use super::*;
use crate::languages::interface::{BoxedField, InterfaceType};

/// The work of writing out the type resources of a sidecar with `impls`
/// inherent `impl` blocks of `methods` methods each, every one owning a
/// struct's option-of-box field.
fn type_resource_work(impls: usize, methods: usize) -> (usize, usize) {
    let mut layouts = BTreeMap::new();
    let cell = crate::languages::rust::names::path_name(&["boxed", "Cell"]);
    layouts.insert(
        cell.clone(),
        RecordLayout::from_explicit_fields(
            vec![("value".into(), InterfaceType::Int32, 0, 4)],
            4,
            4,
        )
        .unwrap(),
    );
    let mut source = String::new();
    for holder in 0..impls {
        let name = crate::languages::rust::names::path_name(&["boxed", &format!("Holder{holder}")]);
        layouts.insert(
            name,
            RecordLayout::from_explicit_fields(
                vec![("slot".into(), InterfaceType::Int32, 0, 4)],
                4,
                4,
            )
            .unwrap()
            .with_boxed_field(
                "slot",
                BoxedField {
                    optional: true,
                    record: cell.clone(),
                },
            ),
        );
        source.push_str(&format!("impl boxed::Holder{holder} {{\n"));
        for method in 0..methods {
            source.push_str(&format!(
                "    fn m{method}(&mut self) {{ owns self.slot; ensures self.slot == 0; }}\n"
            ));
        }
        source.push_str("}\n");
    }
    let (tokens, positions) = tokenizer::tokenize(&source, None).unwrap();
    let length = tokens.len();
    let ((tokens, _, _), work) = crate::instrumentation::measure_deterministic_work(|| {
        write_type_resources(tokens, positions, BTreeSet::new(), &layouts).unwrap()
    });
    // Every method's field gains its type resource, once on each side.
    let derived = tokens
        .iter()
        .filter(|token| matches!(token, Token::Ident(name) if name.starts_with("Option_A")))
        .count();
    assert_eq!(derived, 2 * impls * methods + 1, "{length}");
    (length, work)
}

#[test]
fn type_resources_are_written_in_one_pass_over_the_sidecar() {
    // Doubling the methods of one block, or the blocks, doubles the work:
    // each block's braces are matched once, not once per method.
    for samples in [
        [1, 2, 4, 8].map(|scale| type_resource_work(1, 16 * scale)),
        [1, 2, 4, 8].map(|scale| type_resource_work(16 * scale, 1)),
    ] {
        for pair in samples.windows(2) {
            let ((short, short_work), (long, long_work)) = (pair[0], pair[1]);
            assert!(
                long_work * short <= short_work * long + 64 * long,
                "{samples:?}"
            );
            assert!(long_work <= 4 * long, "{samples:?}");
        }
    }
}
