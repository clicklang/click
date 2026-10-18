//! An index built from the parser's spans holds exactly the proof blocks the
//! parser reads, with the same tactics. The lexical reading of a fragment
//! also takes some braced groups that are not proofs: the arms of a resource
//! declaration's `match`, the branches of an `if` expression in a pure
//! function, and the body of a C function named `open`. Those are counted.

use super::*;

/// Every `.click` source of the examples and mdtests: sidecar files and the
/// `click` blocks of each mdtest.
fn corpus() -> Vec<(String, String)> {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut sources = Vec::new();
    let mut stack = vec![root.join("examples")];
    while let Some(directory) = stack.pop() {
        for entry in std::fs::read_dir(&directory)
            .into_iter()
            .flatten()
            .flatten()
        {
            let path = entry.path();
            if path.is_dir() {
                stack.push(path);
            } else if path
                .extension()
                .is_some_and(|extension| extension == "click")
            {
                let text = std::fs::read_to_string(&path).expect("example reads");
                sources.push((path.display().to_string(), text));
            }
        }
    }
    for entry in std::fs::read_dir(root.join("mdtests"))
        .expect("mdtests")
        .flatten()
    {
        let path = entry.path();
        if path.extension().is_none_or(|extension| extension != "md") {
            continue;
        }
        let text = std::fs::read_to_string(&path).expect("mdtest reads");
        let mut rest = text.as_str();
        let mut block = 0;
        while let Some(start) = rest.find("```click\n") {
            let body = &rest[start + "```click\n".len()..];
            let Some(end) = body.find("\n```") else { break };
            sources.push((
                format!("{}#{block}", path.display()),
                body[..end].to_string(),
            ));
            block += 1;
            rest = &body[end..];
        }
    }
    sources.sort();
    sources
}

#[test]
#[ignore = "nightly: parses the whole corpus"]
fn the_source_index_holds_the_blocks_the_parser_reads() {
    let mut compared = 0;
    let mut unparsed = 0;
    let mut mismatches = Vec::new();
    let mut not_proofs = 0;
    for (name, source) in corpus() {
        // A file that needs C layouts or imported declarations is read by
        // verification, not by this context-free parse.
        let Ok(spans) = parser::parsed_source_spans(&source, parser::ProgramLayouts::default())
        else {
            unparsed += 1;
            continue;
        };
        let Ok(index) = ProofSourceIndex::build(&source, Some(&spans)) else {
            mismatches.push(format!(
                "{name}: the index refuses the parser's proof blocks"
            ));
            continue;
        };
        compared += 1;
        let indexed = index
            .written_blocks()
            .into_iter()
            .map(|(open, close, tactics)| ((open.line, open.column), (close, tactics)))
            .collect::<BTreeMap<_, _>>();
        let mut parsed = BTreeMap::new();
        for span in spans.proof_blocks {
            parsed.insert(
                (span.open.line, span.open.column),
                (span.close, span.tactics),
            );
        }
        for (open, (close, tactics)) in &parsed {
            match indexed.get(open) {
                None => mismatches.push(format!(
                    "{name}:{}:{}: the parser reads a proof block the index misses",
                    open.0, open.1
                )),
                Some((indexed_close, indexed_tactics)) => {
                    let starts = |list: &Vec<SourcePosition>| {
                        list.iter()
                            .map(|position| (position.line, position.column))
                            .collect::<Vec<_>>()
                    };
                    if (indexed_close.line, indexed_close.column) != (close.line, close.column)
                        || starts(indexed_tactics) != starts(tactics)
                    {
                        mismatches.push(format!(
                            "{name}:{}:{}: parser tactics {:?}, index {:?}",
                            open.0,
                            open.1,
                            starts(tactics),
                            starts(indexed_tactics)
                        ));
                    }
                }
            }
        }
        for open in indexed.keys().filter(|open| !parsed.contains_key(open)) {
            mismatches.push(format!(
                "{name}:{}:{}: the index holds a block the parser does not read",
                open.0, open.1
            ));
        }
        if let Ok(fragment) = ProofSourceIndex::new(&source) {
            not_proofs += fragment
                .written_blocks()
                .iter()
                .filter(|(open, _, _)| !parsed.contains_key(&(open.line, open.column)))
                .count();
        }
    }
    eprintln!(
        "compared {compared} sources ({unparsed} need C layouts or imports to parse); \
         a lexical reading takes {not_proofs} braced groups that are not proofs"
    );
    assert!(
        mismatches.is_empty(),
        "{} disagreements:\n{}",
        mismatches.len(),
        mismatches.join("\n")
    );
}
