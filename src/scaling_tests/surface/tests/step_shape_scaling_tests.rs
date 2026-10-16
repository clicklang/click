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

fn partial_borrow_beside_objects(n: usize) -> (String, String) {
    let (c, click) = many_objects(n);
    (
        c.replace("touch(data);", "touch_half(data);"),
        click.replace(
            TOUCH_CLICK,
            "extern void touch_half(int32* data) { owns data[0..2]; }",
        ),
    )
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
            // Each number becomes one `#`, so `x9` and `x10` share a role.
            let mut role = String::new();
            for ch in line.chars() {
                if !ch.is_ascii_digit() {
                    role.push(ch);
                } else if !role.ends_with('#') {
                    role.push('#');
                }
            }
            role
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
    if rises_steadily(work) {
        return true;
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

/// Whether work rises slowly but steadily: over the last half of its
/// positions (at least five), it never falls and rises at three in four of
/// them. A cost of even one unit per earlier statement rises at every
/// position; a logarithmic index rises only where the count doubles, and a
/// warm-up holds once it has jumped. `drifts`' band cannot see the first,
/// which grows by less than the band at each step.
fn rises_steadily(work: &[usize]) -> bool {
    let tail = &work[work.len() - work.len().div_ceil(2)..];
    if tail.len() < 5 {
        return false;
    }
    let changes = tail
        .windows(2)
        .map(|pair| pair[1] as i64 - pair[0] as i64)
        .collect::<Vec<_>>();
    changes.iter().all(|change| *change >= 0)
        && changes.iter().filter(|change| **change > 0).count() * 4 >= changes.len() * 3
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
    assert_no_drift("many_calls", many_calls, 12);
}

#[test]
fn calls_beside_owned_objects_cost_the_same_at_every_position() {
    assert_no_drift("objects_and_calls", objects_and_calls, 12);
}

#[test]
fn ordered_index_stores_cost_the_same_at_every_position() {
    // A store's cost climbs with the stores within about 32 positions of it
    // and then holds: a bounded window, run past so the steady-rise rule
    // sees it level.
    assert_no_drift("order_chain", order_chain, 48);
}

#[test]
fn pointer_field_links_cost_the_same_at_every_position() {
    assert_no_drift("deep_chain", deep_chain, 12);
}

#[test]
fn straight_line_assignments_cost_the_same_at_every_position() {
    assert_no_drift("straight_line", straight_line, 12);
}

#[test]
fn constant_index_stores_cost_the_same_at_every_position() {
    assert_no_drift("const_array", const_array, 12);
}

#[test]
fn calls_to_distinct_callees_cost_the_same_at_every_position() {
    assert_no_drift("many_callees", many_callees, 12);
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

// Splitting a caller's owner must not enumerate the other parameter owners
// that happen to share its external-argument memory block.
#[test]
fn a_partial_borrow_call_ignores_unrelated_owned_objects() {
    assert_flat_across(
        "partial_borrow_beside_objects",
        partial_borrow_beside_objects,
        [1, 8],
        "touch_half(data);",
    );
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
    assert_no_drift("heap_objects", heap_objects, 12);
}

/// A `loop` clause's work does not depend on the loops before it: it reads
/// the contexts and indexes the proof keeps rather than rebuilding them from
/// every earlier loop's facts. Five loops, because the first clause's own
/// warm-up hides a drift among only three.
#[test]
fn sequential_loop_clauses_cost_the_same_at_every_position() {
    let loops = run(loops, 5).loops;
    assert!(
        !drifts(&loops),
        "sequential loop clauses drift with the loops before them: {loops:?}"
    );
}

/// The contexts a `loop` tactic builds, charged or not, do not grow with
/// the loops before it. Its executions copy the path's facts, and their
/// direct-transport context and the initialization proof's indexed facts
/// are the ones the proof keeps, extended by the loop's own facts. Building
/// either from every path fact at each loop (both once did) assumes a further
/// context entry per earlier fact at every loop; the transport context's
/// build is charged nothing, so clause work alone does not show it.
///
/// Across the twelve-loop run, the last clause also costs what the second
/// does. A drift of a unit or two per earlier loop is below the band between
/// neighbours: restoring the entry's blocks at each loop head once rebuilt
/// the block table, and comparing it walked every block declared so far.
#[test]
fn sequential_loops_build_the_same_context_entries_each() {
    let runs = [3, 6, 12].map(|n| {
        let before = crate::kernel::reasoning::path_facts::context_rebuild_entries();
        let run = run(loops, n);
        (
            crate::kernel::reasoning::path_facts::context_rebuild_entries() - before,
            run.loops,
        )
    });
    let entries = runs.each_ref().map(|(entries, _)| *entries);
    let per_loop = [(entries[1] - entries[0]) / 3, (entries[2] - entries[1]) / 6];
    assert!(
        per_loop[1] <= per_loop[0] + band(per_loop[0]),
        "each further loop builds {} context entries at 3 to 6 loops and {} at 6 to 12 \
         ({entries:?})",
        per_loop[0],
        per_loop[1]
    );
    let clauses = &runs[2].1;
    let (second, last) = (clauses[1], clauses[clauses.len() - 1]);
    assert!(
        last <= second + band(second),
        "the last of twelve loop clauses costs {last} where the second costs {second}: \
         {clauses:?}"
    );
}

#[test]
fn drift_rules_separate_slow_drift_from_warm_up() {
    // One unit per earlier statement, too small for the band at any position.
    assert!(drifts(&(300..312).collect::<Vec<_>>()));
    // A warm-up jump, then level.
    assert!(!drifts(&[44, 300, 306, 306, 306, 306, 306, 306, 306, 306]));
    // A bounded window: climbs, then holds over the last half.
    let window = (0..48).map(|i| 300 + 2 * i.min(16)).collect::<Vec<_>>();
    assert!(!drifts(&window));
}
