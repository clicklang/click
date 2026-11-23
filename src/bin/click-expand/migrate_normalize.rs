use std::collections::BTreeMap;
use std::path::Path;

use click::cli::VerificationInput;
use click::surface::{
    ClickProject, NormalizeSourceSite, expand_claim_by_label, first_normalize_in_claim,
    normalize_source_sites, without_proof_search_for_claim,
};

use super::{check_expansion_deadline, verify_proof_unit};

const LEGACY: &str = "normalize";

pub(super) fn run(
    project: Option<&ClickProject>,
    source: &str,
    inputs: &VerificationInput,
    selected: Option<&str>,
    path: &Path,
    line_offset: usize,
) -> Result<String, String> {
    let sites = normalize_source_sites(project, source, &inputs.program_inputs())
        .map_err(|error| error.report())?;
    let mut claims = BTreeMap::<_, Vec<_>>::new();
    for site in &sites {
        if selected.is_none_or(|label| site.claim == label) {
            claims.entry(site.claim.as_str()).or_default().push(site);
        }
    }
    if claims.is_empty() {
        if let Some(label) = selected {
            eprintln!(
                "{}: no written normalization indexed for {label}",
                path.display()
            );
        }
        return Ok(source.to_owned());
    }

    let mut edits = BTreeMap::new();
    for (claim, sites) in claims {
        let result = migrate_claim(project, source, inputs, claim, &sites, &mut edits);
        check_expansion_deadline("migrating written normalization")?;
        let first = sites[0];
        let location = format!(
            "{}:{}:{} in {claim}",
            path.display(),
            line_offset + first.position.line,
            first.position.column,
        );
        match result {
            Ok(()) => eprintln!("{location}: migrated {} call(s)", sites.len()),
            Err(error) => {
                for site in sites {
                    edits.remove(&site.offset);
                }
                eprintln!("{location}: kept original proof\n{error}");
            }
        }
    }
    Ok(apply_edits(source, &edits))
}

fn migrate_claim(
    project: Option<&ClickProject>,
    source: &str,
    inputs: &VerificationInput,
    claim: &str,
    sites: &[&NormalizeSourceSite],
    edits: &mut BTreeMap<usize, &'static str>,
) -> Result<(), String> {
    let verify = |source: &str| {
        verify_proof_unit(project, source, inputs, claim).map_err(|error| error.report())
    };
    verify(&apply_edits(source, edits)).map_err(|error| format!("Original proof: {error}"))?;
    // Most claims can take all of their preferred substitutions in one
    // verification. Retry individual sites only to recover from a miss.
    edits.extend(
        sites
            .iter()
            .map(|site| (site.offset, if site.using { "solve" } else { "known" })),
    );
    if let Err(error) = verify(&apply_edits(source, edits)) {
        if sites.iter().all(|site| site.using) {
            return Err(format!("Replacement proof: {error}"));
        }
        for site in sites {
            edits.remove(&site.offset);
        }
        for site in sites {
            if !site.using {
                edits.insert(site.offset, "known");
                if verify(&apply_edits(source, edits)).is_ok() {
                    continue;
                }
            }
            edits.insert(site.offset, "solve");
            verify(&apply_edits(source, edits))
                .map_err(|error| format!("Replacement proof: {error}"))?;
        }
    }

    let candidate = apply_edits(source, edits);
    let candidate_project = project.map(|project| project.with_entry_source(candidate.clone()));
    require_no_normalize(
        candidate_project.as_ref(),
        &candidate,
        inputs,
        claim,
        "Replacement proof",
    )?;
    let expanded = expand_claim_by_label(
        candidate_project.as_ref(),
        &candidate,
        &inputs.program_inputs(),
        claim,
        None,
    )
    .map_err(|error| format!("Expansion: {}", error.report()))?;
    if expanded.proof_unit != claim {
        return Err(format!(
            "Expansion selected a different proof unit: {}",
            expanded.proof_unit
        ));
    }
    let expanded_project =
        project.map(|project| project.with_entry_source(expanded.source.clone()));
    require_no_normalize(
        expanded_project.as_ref(),
        &expanded.source,
        inputs,
        claim,
        "Expanded proof",
    )?;
    without_proof_search_for_claim(claim, || verify(&expanded.source))
        .map_err(|error| format!("Strict replay: {error}"))
}

fn require_no_normalize(
    project: Option<&ClickProject>,
    source: &str,
    inputs: &VerificationInput,
    claim: &str,
    stage: &str,
) -> Result<(), String> {
    if let Some(position) =
        first_normalize_in_claim(project, source, &inputs.program_inputs(), claim)
            .map_err(|error| format!("{stage}: {}", error.report()))?
    {
        let before = position.line.saturating_sub(4);
        let context = source
            .lines()
            .skip(before)
            .take(position.line - before)
            .collect::<Vec<_>>()
            .join("\n");
        return Err(format!(
            "{stage} still contains normalize() at {}:{} in its Click source\n{context}",
            position.line, position.column
        ));
    }
    Ok(())
}

fn apply_edits(source: &str, edits: &BTreeMap<usize, &'static str>) -> String {
    let mut output = String::with_capacity(source.len());
    let mut from = 0;
    for (&offset, replacement) in edits {
        output.push_str(&source[from..offset]);
        output.push_str(replacement);
        from = offset + LEGACY.len();
    }
    output.push_str(&source[from..]);
    output
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn migrates_passing_claims_and_keeps_an_unproved_claim() {
        let source = r#"
theorem immediate(x: int32) {
    // normalize() in a comment should stay.
    ensures x == x by normalize();
}
theorem with_premise(x: int32) {
    requires x == 0;
    ensures x == 0 by { normalize() using { x == 0; }; }
}
theorem broken(x: int32) {
    ensures x == 0 by normalize();
}
"#;
        let migrated = run(
            None,
            source,
            &VerificationInput::Bundle(Vec::new()),
            None,
            Path::new("migration.click"),
            0,
        )
        .unwrap();
        assert_eq!(
            migrated,
            source
                .replace(
                    "ensures x == x by normalize();",
                    "ensures x == x by known();"
                )
                .replace("normalize() using { x == 0; }", "solve() using { x == 0; }")
        );
    }
}
