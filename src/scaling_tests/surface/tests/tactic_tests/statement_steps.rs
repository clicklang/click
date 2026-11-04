use super::*;

#[test]
fn explicit_adjacent_pointer_frames_compose_without_history_search() {
    let mut samples = Vec::new();
    for size in [2, 4, 8, 16, 32] {
        let mut c =
            String::from("struct job { int *output; }; void write(struct job *job, int *dest) {\n");
        let mut click = String::from(
            r#"
verifying "probe.c";
void write(struct job *job, int32 *dest) {
    views job->output;
    owns dest[0..1];
    requires separate(memory(job->output), memory(dest[0..1]));
    ensures job->output == old(job->output);
} by {
    mark entry;
"#,
        );
        for index in 0..size {
            c.push_str(&format!("*dest = {index};\n"));
            click.push_str(&format!(
                r#"
    mark before_{index};
    step();
    mark after_{index};
    have job->output == at(before_{index}, job->output) by {{
        transport_certificate {{
            premise 0: changes_only(before_{index}, after_{index}, memory(dest[0..1]))
                => changes_only(before_{index}, after_{index}, memory(dest[0..1]));
            premise 1: at(entry, separate(memory(job->output), memory(dest[0..1])))
                => at(entry, separate(memory(job->output), memory(dest[0..1])));
            preserve 0, 1 => job->output == at(before_{index}, job->output);
            conclusion 2;
        }}
    }}
"#
            ));
            if index > 0 {
                click.push_str(&format!(
                    r#"
    have job->output == at(entry, job->output) by {{
        transport_certificate {{
            premise 0: job->output == at(before_{index}, job->output)
                => job->output == at(before_{index}, job->output);
            premise 1: at(before_{index}, job->output) == at(entry, job->output)
                => at(before_{index}, job->output) == at(entry, job->output);
            transitive 0, 1 => job->output == at(entry, job->output);
            conclusion 2;
        }}
    }}
"#
                ));
            }
        }
        c.push_str("}\n");
        click.push_str("step();\n}\n");
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::surface::without_implicit_auto(|| verify_c0_sources(&click, &[("probe.c", &c)]))
        });
        result.unwrap_or_else(|error| panic!("size {size}: {error}\n{click}"));
        if size != 2 {
            samples.push((size, work));
        }
    }
    eprintln!("Surface explicit pointer frames: {samples:?}");
    for pair in samples.windows(2) {
        assert!(pair[1].1 <= pair[0].1 * 3, "{samples:?}");
    }
}

/// Obligation discovery must retain the call result, rather than applying all
/// postconditions a second time. Grow the selected contract as well as unrelated
/// input facts; count kernel executions and charged work, not wall time.
#[test]
#[ignore = "nightly: nine prepared-call proofs across contract and context sizes"]
fn prepared_call_obligations_execute_once_as_contract_and_context_grow() {
    for mode in ["bare", "by", "requires"] {
        let mut samples = Vec::new();
        for size in [1, 8, 32] {
            let conditions = (1..=size)
                .map(|n| format!("ensures result != -{n};\n"))
                .collect::<String>();
            let ambient = (1..=size)
                .map(|n| format!("requires unrelated != -{n};\n"))
                .collect::<String>();
            let body = "have positive(a) == 1 by { unfold(positive(a)); normalize() using { a > 0; }; } assumption();";
            let step = if mode == "bare" {
                "step();".to_string()
            } else if mode == "by" {
                format!("step() by {{ {body} }}")
            } else {
                format!("step() {{ requires positive(a) == 1 by {{ {body} }} }}")
            };
            let source = format!(
                r#"
verifying "call.c";
function positive(x: int32) -> int32 {{ if x > 0 {{ 1 }} else {{ 0 }} }}
extern int32 callee(int32 x) {{
    requires positive(x) == 1;
    ensures result == x;
    {conditions}
}}
int32 caller(int32 a, int32 unrelated) {{
    requires a > 0;
    {ambient}
    ensures result == a;
}} by {{
    {step}
    have positive(a) == 1 by assumption();
    step(); solve();
}}
"#
            );
            let ((result, work), events) = crate::instrumentation::collect(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    verify_c0_sources(
                        &source,
                        &[(
                            "call.c",
                            "int32 caller(int32 a, int32 unrelated) { return callee(a); }",
                        )],
                    )
                })
            });
            result.unwrap_or_else(|error| panic!("{mode}, {size}: {error}"));
            let applications = events
                .iter()
                .filter(|event| {
                    matches!(event,
                        crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                        if name == "verification statement: call assign"
                    )
                })
                .count();
            assert_eq!(
                applications, 1,
                "{mode}, {size}: a prepared call must not execute twice"
            );
            samples.push((size, work));
        }
        eprintln!("prepared {mode} call work: {samples:?}");
        for pair in samples.windows(2) {
            assert!(
                pair[1].1 * pair[0].0 <= pair[0].1 * pair[1].0 * 2,
                "prepared-call work must remain near-linear: {samples:?}"
            );
        }
    }
}
