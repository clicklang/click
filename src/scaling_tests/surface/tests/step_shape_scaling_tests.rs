//! End-to-end step scaling: one C function per shape and size, checked with
//! one explicit simple tactic per statement, so each step's deterministic
//! work can be compared across sizes. A simple step must cost work bounded by
//! its own statement and the state it changes, not by the function's size
//! (`docs/internals/verification-efficiency.md`, and "Scaling tests" in
//! `docs/internals/testing.md`). These are the shapes of
//! `scripts/step-scaling-hunt.py` at gate sizes, with an extern callee and no
//! closing proof to keep them fast; the script runs the full versions at
//! larger sizes for investigation.

use super::*;

const TOUCH_C: &str = "";
// An extern contract: the call takes the same contract-application path as a
// verified callee's, without spending the test's time verifying its body.
const TOUCH_CLICK: &str = "extern void touch(int32* data) {
    owns data[0..4];
}";

fn lines(count: usize, line: impl Fn(usize) -> String) -> String {
    (0..count).map(line).collect::<Vec<_>>().join("\n")
}

fn steps(count: usize) -> String {
    lines(count, |_| "    step();".to_string())
}

fn many_calls(n: usize) -> (String, String) {
    let calls = lines(n, |_| "    touch(data);".into());
    let c = format!(
        "struct box {{
    int32 v;
}};

{TOUCH_C}

int32 caller(int32* data, struct box* b) {{
    b->v = 5;
{calls}
    return b->v;
}}"
    );
    let steps = steps(n + 2);
    let click = format!(
        "verifying \"hunt.c\";

{TOUCH_CLICK}

int32 caller(int32* data, struct box* b) {{
    owns data[0..4];
    owns *b;
}} by {{
{steps}
}}"
    );
    (c, click)
}

fn many_objects_with_calls(n: usize, calls: usize) -> (String, String) {
    let params = (0..n)
        .map(|i| format!("struct box* b{i}"))
        .collect::<Vec<_>>()
        .join(", ");
    let sets = lines(n, |i| format!("    b{i}->v = {i};"));
    let body_calls = lines(calls, |_| "    touch(data);".into());
    let reads = (0..n)
        .map(|i| format!("b{i}->v"))
        .collect::<Vec<_>>()
        .join(" + ");
    let c = format!(
        "struct box {{
    int32 v;
}};

{TOUCH_C}

int32 caller(int32* data, {params}) {{
    int32 total;
{sets}
{body_calls}
    total = {reads};
    return total;
}}"
    );
    let owns = lines(n, |i| format!("    owns *b{i};"));
    let steps = steps(1 + n + calls + 2);
    let click = format!(
        "verifying \"hunt.c\";

{TOUCH_CLICK}

int32 caller(int32* data, {params}) {{
    owns data[0..4];
{owns}
}} by {{
{steps}
}}"
    );
    (c, click)
}

fn many_objects(n: usize) -> (String, String) {
    many_objects_with_calls(n, 1)
}

fn objects_and_calls(n: usize) -> (String, String) {
    many_objects_with_calls(n, n)
}

fn aliases(n: usize) -> (String, String) {
    let params = (0..n)
        .map(|i| format!("struct box* q{i}"))
        .collect::<Vec<_>>()
        .join(", ");
    let reads = (0..n)
        .map(|i| format!("q{i}->v"))
        .collect::<Vec<_>>()
        .join(" + ");
    let c = format!(
        "struct box {{
    int32 v;
}};

{TOUCH_C}

int32 caller(int32* data, struct box* b, {params}) {{
    int32 total;
    b->v = 1;
    touch(data);
    total = {reads};
    return total;
}}"
    );
    let requires = lines(n, |i| format!("    requires q{i} == b;"));
    let steps = steps(5);
    let click = format!(
        "verifying \"hunt.c\";

{TOUCH_CLICK}

int32 caller(int32* data, struct box* b, {params}) {{
    owns data[0..4];
    owns *b;
{requires}
}} by {{
{steps}
}}"
    );
    (c, click)
}

fn order_chain(n: usize) -> (String, String) {
    let params = (0..=n)
        .map(|i| format!("int32 x{i}"))
        .collect::<Vec<_>>()
        .join(", ");
    let stores = lines(n, |i| format!("    data[x{}] = {};", i + 1, i + 1));
    let c = format!(
        "int32 caller(int32* data, int32 len, {params}) {{
    int32 first;
    data[x0] = 100;
{stores}
    first = data[x0];
    return first;
}}"
    );
    let requires = lines(n, |i| format!("    requires x{i} < x{};", i + 1));
    let steps = steps(1 + 1 + n + 2);
    let click = format!(
        "verifying \"hunt.c\";

int32 caller(int32* data, int32 len, {params}) {{
    owns data[0..len];
    requires 0 <= x0;
{requires}
    requires x{n} < len;
}} by {{
{steps}
}}"
    );
    (c, click)
}

fn deep_chain(n: usize) -> (String, String) {
    let params = (0..=n)
        .map(|i| format!("struct node* n{i}"))
        .collect::<Vec<_>>()
        .join(", ");
    let links = lines(n, |i| format!("    n{i}->next = n{};", i + 1));
    let path = format!("n0{}", "->next".repeat(n));
    let c = format!(
        "struct node {{
    struct node* next;
    int32 v;
}};

{TOUCH_C}

int32 caller(int32* data, {params}) {{
    int32 out;
{links}
    n{n}->v = 9;
    touch(data);
    out = {path}->v;
    return out;
}}"
    );
    let owns = lines(n + 1, |i| format!("    owns *n{i};"));
    let steps = steps(1 + n + 1 + 1 + 2);
    let click = format!(
        "verifying \"hunt.c\";

{TOUCH_CLICK}

int32 caller(int32* data, {params}) {{
    owns data[0..4];
{owns}
}} by {{
{steps}
}}"
    );
    (c, click)
}

fn branches(n: usize) -> (String, String) {
    let ifs = lines(n, |i| {
        format!(
            "    if (a{i} > 0) {{
        s = s + 1;
    }}"
        )
    });
    let params = (0..n)
        .map(|i| format!("int32 a{i}"))
        .collect::<Vec<_>>()
        .join(", ");
    let c = format!(
        "int32 caller({params}) {{
    int32 s;
    s = 0;
{ifs}
    return s;
}}"
    );
    let arms = lines(n, |i| {
        let bound = i + 1;
        format!(
            "        branch ensuring {{
            fact 0 <= s;
            fact s <= {bound};
        }} then {{
            step();
            have 0 <= s by {{ simp(); }}
            have s <= {bound} by {{ simp(); }}
        }} else {{
            have s <= {bound} by {{ simp(); }}
        }}"
        )
    });
    let click = format!(
        "verifying \"hunt.c\";

int32 caller({params}) {{
    ensures result >= 0 by {{
        step();
        step();
{arms}
        step();
        simp();
    }}
}}"
    );
    (c, click)
}

fn straight_line(n: usize) -> (String, String) {
    let decls = lines(n, |i| format!("    int32 x{};", i + 1));
    let assigns = lines(n, |i| format!("    x{} = x{i} + 1;", i + 1));
    let c = format!(
        "int32 caller(int32 x0) {{
{decls}
{assigns}
    return x{n};
}}"
    );
    let steps = steps(2 * n + 1);
    let click = format!(
        "verifying \"hunt.c\";

int32 caller(int32 x0) {{
    requires 0 <= x0;
    requires x0 <= 1000000;
    ensures true;
}} by {{
{steps}
}}"
    );
    (c, click)
}

fn loops(n: usize) -> (String, String) {
    let body = lines(n, |k| {
        format!(
            "    i = 0;
    while (i < 4) {{
        p[i] = {k};
        i = i + 1;
    }}"
        )
    });
    let c = format!(
        "int32 caller(int32* p) {{
    int32 i;
{body}
    return 0;
}}"
    );
    let proof = lines(n, |_| {
        "    step();
    loop { decreases 4 - i; invariant i >= 0; invariant i <= 4; }"
            .into()
    });
    let click = format!(
        "verifying \"hunt.c\";

int32 caller(int32* p) {{
    owns p[0..4];
    ensures result == 0;
}} by {{
    step();
{proof}
    step();
    simp();
}}"
    );
    (c, click)
}

fn const_array(n: usize) -> (String, String) {
    let stores = lines(n, |i| format!("    data[{i}] = {i};"));
    let c = format!(
        "int32 caller(int32* data) {{
    int32 first;
{stores}
    first = data[0];
    return first;
}}"
    );
    let steps = steps(n + 3);
    let click = format!(
        "verifying \"hunt.c\";

int32 caller(int32* data) {{
    owns data[0..{n}];
}} by {{
{steps}
}}"
    );
    (c, click)
}

fn many_callees(n: usize) -> (String, String) {
    let callees_c = (0..n)
        .map(|i| {
            format!(
                "void touch{i}(int32* data) {{
    return;
}}"
            )
        })
        .collect::<Vec<_>>()
        .join("\n\n");
    let calls = lines(n, |i| format!("    touch{i}(data);"));
    let c = format!(
        "struct box {{
    int32 v;
}};

{callees_c}

int32 caller(int32* data, struct box* b) {{
    b->v = 5;
{calls}
    return b->v;
}}"
    );
    let callees_click = (0..n)
        .map(|i| {
            format!(
                "void touch{i}(int32* data) {{
    owns data[0..4];
}} by {{
    execute();
    simp();
}}"
            )
        })
        .collect::<Vec<_>>()
        .join("\n\n");
    let steps = steps(n + 2);
    let click = format!(
        "verifying \"hunt.c\";

{callees_click}

int32 caller(int32* data, struct box* b) {{
    owns data[0..4];
    owns *b;
}} by {{
{steps}
}}"
    );
    (c, click)
}

fn unrelated_facts(n: usize) -> (String, String) {
    let params = (0..n)
        .map(|i| format!("int32 a{i}"))
        .collect::<Vec<_>>()
        .join(", ");
    let requires = lines(n, |i| format!("    requires a{i} < {};", i + 1000));
    let c = format!(
        "struct box {{
    int32 v;
}};

{TOUCH_C}

int32 caller(int32* data, struct box* b, {params}) {{
    b->v = 5;
    touch(data);
    return b->v;
}}"
    );
    let click = format!(
        "verifying \"hunt.c\";

{TOUCH_CLICK}

int32 caller(int32* data, struct box* b, {params}) {{
    owns data[0..4];
    owns *b;
{requires}
}} by {{
    step();
    step();
    step();
}}"
    );
    (c, click)
}

fn heap_objects(n: usize) -> (String, String) {
    let decls = lines(n, |i| format!("    struct box* p{i};"));
    let makes = lines(n, |i| format!("    p{i} = make_box();\n    p{i}->v = {i};"));
    let drops = lines(n, |i| format!("    drop_box(p{i});"));
    let c = format!(
        "struct box {{
    int32 v;
}};

int32 caller() {{
{decls}
{makes}
{drops}
    return 0;
}}"
    );
    let make_proof = lines(n, |i| {
        format!(
            "    step();
    unfold(boxed(p{i}));
    step();
    fold(boxed(p{i}));"
        )
    });
    let steps = steps(n);
    let click = format!(
        "verifying \"hunt.c\";

resource boxed(p: struct box*) {{
    owns *p;
}}

extern struct box* make_box() {{
    produces boxed(result);
}}

extern void drop_box(struct box* p) {{
    consumes boxed(p);
}}

int32 caller() {{
    ensures true;
}} by {{
{steps}
{make_proof}
{steps}
    step();
}}"
    );
    (c, click)
}

/// One verified size of a shape: each `step()`'s work in proof order beside
/// the statement it executes with digits blanked, so that steps doing the
/// same thing at different positions share a role, each `loop` clause's
/// work, and each other simple resource tactic's work in proof order by
/// tactic. The steps execute `caller`'s statements in source order, one each.
struct Run {
    statements: usize,
    steps: Vec<(String, usize)>,
    loops: Vec<usize>,
    resource_tactics: Vec<(&'static str, Vec<usize>)>,
}

impl Run {
    /// The steps, each beside the statement it executes; refuses a run whose
    /// steps do not pair one to one with `caller`'s statements.
    fn statement_steps(&self, name: &str) -> &[(String, usize)] {
        assert_eq!(
            self.steps.len(),
            self.statements,
            "{name}: expected one step per statement"
        );
        &self.steps
    }
}

/// The simple tactics besides `step` a shape's proof repeats per object:
/// each must cost the same at every position, as a step must.
const RESOURCE_TACTICS: [&str; 2] = ["unfold", "fold"];

fn run(shape: fn(usize) -> (String, String), n: usize) -> Run {
    let (c, click) = shape(n);
    let (result, samples) = crate::instrumentation::collect_tactic_work(|| {
        verify_c0_sources(&click, &[("hunt.c", c.as_str())])
    });
    result.unwrap_or_else(|error| panic!("size {n}: {}", error.message()));
    let body = c
        .split("caller(")
        .nth(1)
        .expect("the shape defines `caller`");
    let roles = body
        .lines()
        .skip(1)
        .map(str::trim)
        .filter(|line| line.ends_with(';'))
        .map(|line| {
            line.chars()
                .map(|ch| if ch.is_ascii_digit() { '#' } else { ch })
                .collect::<String>()
        })
        .collect::<Vec<_>>();
    let in_order = |name: &str| {
        // A `loop` clause also reports its own nested bookkeeping at the same
        // index; the clause is the larger.
        let mut work = BTreeMap::<usize, usize>::new();
        for sample in samples.iter().filter(|sample| {
            sample.tactic.claim.contains("caller") && sample.tactic.tactic_name == name
        }) {
            let entry = work.entry(sample.tactic.tactic_index).or_default();
            *entry = (*entry).max(sample.work);
        }
        work.into_values().collect::<Vec<_>>()
    };
    Run {
        statements: roles.len(),
        steps: in_order("step")
            .into_iter()
            .enumerate()
            .map(|(index, work)| (roles.get(index).cloned().unwrap_or_default(), work))
            .collect(),
        loops: in_order("loop"),
        resource_tactics: RESOURCE_TACTICS
            .into_iter()
            .map(|name| (name, in_order(name)))
            .collect(),
    }
}

/// Work differences this small are not drift: a logarithmic index lookup
/// changes by at most a unit or two between adjacent positions, and a
/// one-off change in spelling does not repeat. A cost linear in earlier
/// statements, even four units per position on a step of 150, exceeds it.
fn band(work: usize) -> usize {
    2 + work / 256
}

/// Whether work along successive positions drifts: its last changes (three,
/// or two over three positions) all move the same way by more than `band`.
/// A step whose cost depends on how many earlier statements ran changes by
/// about the same amount at every position; a warm-up (the first call, the
/// first store into a block) jumps once and then holds.
fn drifts(work: &[usize]) -> bool {
    if work.len() < 3 {
        return false;
    }
    let tail = &work[work.len() - work.len().min(4)..];
    let changes = tail
        .windows(2)
        .map(|pair| pair[1] as i64 - pair[0] as i64)
        .collect::<Vec<_>>();
    let large = |change: i64, at: usize| change.unsigned_abs() as usize > band(at);
    changes
        .iter()
        .zip(&tail[1..])
        .all(|(change, at)| *change > 0 && large(*change, *at))
        || changes
            .iter()
            .zip(&tail[1..])
            .all(|(change, at)| *change < 0 && large(*change, *at))
}

/// The roles of `run` whose steps or resource tactics drift, with their
/// work.
fn drifting_roles(name: &str, run: &Run) -> Vec<(String, Vec<usize>)> {
    let mut roles = BTreeMap::<String, Vec<usize>>::new();
    for (role, work) in run.statement_steps(name) {
        roles.entry(role.clone()).or_default().push(*work);
    }
    for (tactic, work) in &run.resource_tactics {
        roles.insert(format!("{tactic} tactic"), work.clone());
    }
    roles.into_iter().filter(|(_, work)| drifts(work)).collect()
}

/// A shape whose repeated statements must each cost the same at every
/// position, verified once at `n`.
fn assert_no_drift(name: &str, shape: fn(usize) -> (String, String), n: usize) {
    let drifting = drifting_roles(name, &run(shape, n));
    assert!(
        drifting.is_empty(),
        "{name} at {n}: a step's work drifts with the statements before it \
         (issues/scaling.md): {drifting:?}"
    );
}

/// The largest work of the steps executing `role` at each size, which must
/// not grow beyond `band` between the sizes: the shape grows state the step
/// does not touch.
fn assert_flat_across(
    name: &str,
    shape: fn(usize) -> (String, String),
    sizes: [usize; 2],
    role: &str,
) {
    let largest = sizes.map(|n| {
        run(shape, n)
            .statement_steps(name)
            .iter()
            .filter(|(step, _)| step == role)
            .map(|(_, work)| *work)
            .max()
            .unwrap_or_else(|| panic!("{name} at {n}: no `{role}` step"))
    });
    assert!(
        largest[1] <= largest[0] + band(largest[0]),
        "{name}: `{role}` grows from {} to {} between sizes {} and {}, with state it does \
         not touch (issues/scaling.md)",
        largest[0],
        largest[1],
        sizes[0],
        sizes[1]
    );
}

#[test]
fn repeated_calls_cost_the_same_at_every_position() {
    assert_no_drift("many_calls", many_calls, 5);
}

#[test]
fn calls_beside_owned_objects_cost_the_same_at_every_position() {
    assert_no_drift("objects_and_calls", objects_and_calls, 4);
}

#[test]
fn ordered_index_stores_cost_the_same_at_every_position() {
    assert_no_drift("order_chain", order_chain, 8);
}

#[test]
fn pointer_field_links_cost_the_same_at_every_position() {
    assert_no_drift("deep_chain", deep_chain, 5);
}

#[test]
fn straight_line_assignments_cost_the_same_at_every_position() {
    assert_no_drift("straight_line", straight_line, 8);
}

#[test]
fn constant_index_stores_cost_the_same_at_every_position() {
    assert_no_drift("const_array", const_array, 8);
}

#[test]
fn calls_to_distinct_callees_cost_the_same_at_every_position() {
    assert_no_drift("many_callees", many_callees, 5);
}

#[test]
fn a_call_ignores_unrelated_facts() {
    assert_flat_across("unrelated_facts", unrelated_facts, [1, 3], "touch(data);");
}

#[test]
fn a_call_ignores_aliases_of_an_owned_object() {
    assert_flat_across("aliases", aliases, [1, 3], "touch(data);");
}

#[test]
fn a_call_ignores_unrelated_owned_objects() {
    assert_flat_across("many_objects", many_objects, [1, 3], "touch(data);");
}

#[test]
fn a_branch_arm_step_ignores_earlier_branches() {
    let largest = [1, 3].map(|n| {
        let (c, click) = branches(n);
        let (result, samples) = crate::instrumentation::collect_tactic_work(|| {
            verify_c0_sources(&click, &[("hunt.c", c.as_str())])
        });
        result.unwrap_or_else(|error| panic!("branches at {n}: {}", error.message()));
        samples
            .iter()
            .filter(|sample| sample.tactic.tactic_name == "step")
            .map(|sample| sample.work)
            .max()
            .expect("branch steps")
    });
    assert!(
        largest[1] <= largest[0] + band(largest[0]),
        "branches: the largest step grows from {} to {} (issues/scaling.md)",
        largest[0],
        largest[1]
    );
}

#[test]
fn heap_object_stores_and_releases_cost_the_same_at_every_position() {
    assert_no_drift("heap_objects", heap_objects, 4);
}

/// Known growth, recorded so that it is measured on every change and a fix
/// is noticed: when one of these stops drifting, make it an ordinary
/// no-drift test here and delete the cause from `issues/scaling.md` or the
/// bug it names.
/// `bugs/sequential-loop-clause-grows-with-earlier-loops.md`.
#[test]
fn known_drift_sequential_loop_clauses() {
    let loops = run(loops, 3).loops;
    assert!(
        drifts(&loops),
        "sequential loop clauses stopped drifting ({loops:?}); delete this test and the bug \
         `sequential-loop-clause-grows-with-earlier-loops.md`"
    );
}
