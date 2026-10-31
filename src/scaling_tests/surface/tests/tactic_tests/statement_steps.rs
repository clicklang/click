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
