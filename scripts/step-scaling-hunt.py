#!/usr/bin/env python3
"""Hunt for C shapes whose simple `step` work grows with unrelated state.

A simple tactic must cost work proportional to its own input and the C
operation it executes (docs/internals/verification-efficiency.md). Each shape
below generates one natural C function and an explicit one-`step()`-per-
statement proof at several sizes N, verifies it with `CLICK_TIMINGS`, and
prints every step's deterministic work. A shape whose per-step work stays flat
as N grows is fine; one whose largest step grows is a perverse function: a
program `step` cannot check at a cost proportional to the line being checked.

    python3 scripts/step-scaling-hunt.py [SHAPE ...] [--sizes 1,4,16,64,128]

Uses the optimized verifier at `$CARGO_TARGET_DIR/profiling/click` (build it
with `cargo build --profile profiling --bin click`). Generated mdtests are
kept under a temporary directory, printed at the end, for reproduction.
"""
import argparse
import os
import re
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CLICK = os.path.join(os.environ.get("CARGO_TARGET_DIR", os.path.join(ROOT, "target")), "profiling", "click")


def mdtest(title, c, click):
    return f"# {title}\n\n```c filename=hunt.c\n{c}\n```\n\n```click\n{click}\n```\n\n```expect\npass\n```\n"

def many_calls(n):
    calls = "\n".join("    touch(flags, data, k);" for _ in range(n))
    c = f"""struct box {{
    int32 v;
}};

void touch(int32* flags, int32* data, int32 k) {{
    return;
}}

int32 caller(int32* flags, int32* data, int32 k, struct box* b) {{
    b->v = 5;
{calls}
    return b->v;
}}"""
    steps = "\n".join("    step();" for _ in range(n + 2))
    click = f"""verifying "hunt.c";

void touch(int32* flags, int32* data, int32 k) {{
    owns flags[0..k];
    owns data[0..k];
}} by {{
    execute();
    simp();
}}

int32 caller(int32* flags, int32* data, int32 k, struct box* b) {{
    owns flags[0..k];
    owns data[0..k];
    owns *b;
    ensures result == 5;
}} by {{
{steps}
    simp();
}}"""
    return mdtest(f"many calls {n}", c, click)


def many_objects(n, calls=1):
    params = ", ".join(f"struct box* b{i}" for i in range(n))
    sets = "\n".join(f"    b{i}->v = {i};" for i in range(n))
    body_calls = "\n".join("    touch(flags, data, k);" for _ in range(calls))
    reads = " + ".join(f"b{i}->v" for i in range(n))
    c = f"""struct box {{
    int32 v;
}};

void touch(int32* flags, int32* data, int32 k) {{
    return;
}}

int32 caller(int32* flags, int32* data, int32 k, {params}) {{
    int32 total;
{sets}
{body_calls}
    total = {reads};
    return total;
}}"""
    owns = "\n".join(f"    owns *b{i};" for i in range(n))
    expected = sum(range(n))
    steps = "\n".join("    step();" for _ in range(1 + n + calls + 2))
    click = f"""verifying "hunt.c";

void touch(int32* flags, int32* data, int32 k) {{
    owns flags[0..k];
    owns data[0..k];
}} by {{
    execute();
    simp();
}}

int32 caller(int32* flags, int32* data, int32 k, {params}) {{
    owns flags[0..k];
    owns data[0..k];
{owns}
    ensures result == {expected};
}} by {{
{steps}
    simp();
}}"""
    return mdtest(f"many objects {n}", c, click)

def objects_and_calls(n):
    return many_objects(n, calls=n)

SHAPES = {'many_calls': many_calls, 'many_objects': many_objects, 'objects_and_calls': objects_and_calls}

TOUCH_C = """void touch(int32* flags, int32* data, int32 k) {
    return;
}"""
TOUCH_CLICK = """void touch(int32* flags, int32* data, int32 k) {
    owns flags[0..k];
    owns data[0..k];
} by {
    execute();
    simp();
}"""

def aliases(n):
    params = ", ".join(f"struct box* q{i}" for i in range(n))
    reads = " + ".join(f"q{i}->v" for i in range(n))
    c = f"""struct box {{
    int32 v;
}};

{TOUCH_C}

int32 caller(int32* flags, int32* data, int32 k, struct box* b, {params}) {{
    int32 total;
    b->v = 1;
    touch(flags, data, k);
    total = {reads};
    return total;
}}"""
    requires = "\n".join(f"    requires q{i} == b;" for i in range(n))
    steps = "\n".join("    step();" for _ in range(5))
    click = f"""verifying "hunt.c";

{TOUCH_CLICK}

int32 caller(int32* flags, int32* data, int32 k, struct box* b, {params}) {{
    owns flags[0..k];
    owns data[0..k];
    owns *b;
{requires}
    ensures result == {n};
}} by {{
{steps}
    simp();
}}"""
    return mdtest(f"aliases {n}", c, click)

def order_chain(n):
    params = ", ".join(f"int32 x{i}" for i in range(n + 1))
    stores = "\n".join(f"    data[x{i}] = {i};" for i in range(1, n + 1))
    c = f"""int32 caller(int32* data, int32 len, {params}) {{
    int32 first;
    data[x0] = 100;
{stores}
    first = data[x0];
    return first;
}}"""
    requires = "\n".join(f"    requires x{i} < x{i+1};" for i in range(n))
    steps = "\n".join("    step();" for _ in range(1 + 1 + n + 2))
    click = f"""verifying "hunt.c";

int32 caller(int32* data, int32 len, {params}) {{
    owns data[0..len];
    requires 0 <= x0;
{requires}
    requires x{n} < len;
    ensures result == 100;
}} by {{
{steps}
    simp();
}}"""
    return mdtest(f"order chain {n}", c, click)

def deep_chain(n):
    params = ", ".join(f"struct node* n{i}" for i in range(n + 1))
    links = "\n".join(f"    n{i}->next = n{i+1};" for i in range(n))
    path = "n0" + "->next" * n
    c = f"""struct node {{
    struct node* next;
    int32 v;
}};

{TOUCH_C}

int32 caller(int32* flags, int32* data, int32 k, {params}) {{
    int32 out;
{links}
    n{n}->v = 9;
    touch(flags, data, k);
    out = {path}->v;
    return out;
}}"""
    owns = "\n".join(f"    owns *n{i};" for i in range(n + 1))
    steps = "\n".join("    step();" for _ in range(1 + n + 1 + 1 + 2))
    click = f"""verifying "hunt.c";

{TOUCH_CLICK}

int32 caller(int32* flags, int32* data, int32 k, {params}) {{
    owns flags[0..k];
    owns data[0..k];
{owns}
    ensures result == 9;
}} by {{
{steps}
    simp();
}}"""
    return mdtest(f"deep chain {n}", c, click)

SHAPES.update({'aliases': aliases, 'order_chain': order_chain, 'deep_chain': deep_chain})



STEP = re.compile(r"click timing: tactic caller\S* \d+ step class simple .* ([0-9.]+)s work (\d+)")


def verify(path):
    out = subprocess.run(
        [CLICK, "verify", path],
        env=dict(os.environ, CLICK_TIMINGS="1", RUST_MIN_STACK="8388608"),
        capture_output=True,
        text=True,
    )
    steps = [
        (int(m.group(2)), float(m.group(1)))
        for m in map(STEP.match, (out.stdout + out.stderr).splitlines())
        if m
    ]
    return out.returncode == 0, steps, out.stdout + out.stderr


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("shapes", nargs="*", default=list(SHAPES))
    parser.add_argument("--sizes", default="1,4,16,64,128")
    args = parser.parse_args()
    sizes = [int(size) for size in args.sizes.split(",")]
    if not os.access(CLICK, os.X_OK):
        sys.exit(f"error: no optimized verifier at {CLICK}; run `cargo build --profile profiling --bin click`")
    directory = tempfile.mkdtemp(prefix="click-step-hunt.")
    for shape in args.shapes:
        largest = []
        mean_ms = []
        for n in sizes:
            path = os.path.join(directory, f"{shape}_{n}.md")
            with open(path, "w") as handle:
                handle.write(SHAPES[shape](n))
            ok, steps, output = verify(path)
            if not ok or not steps:
                print(f"{shape:18} N={n:<4} did not verify: {path}")
                print(output[-1500:])
                break
            work = [units for units, _ in steps]
            largest.append(max(work))
            mean_ms.append(1000 * sum(seconds for _, seconds in steps) / len(steps))
            print(
                f"{shape:18} N={n:<4} steps={len(steps):<4} total={sum(work):<9} "
                f"largest step={max(work):<7} mean step={mean_ms[-1]:.2f} ms"
            )
        if len(largest) >= 2:
            # Work is deterministic. Time also catches costs no work budget
            # charges, such as hashing; it is compared from the second size,
            # past the first sizes' fixed overhead, and is noisier.
            growth = largest[-1] / largest[0]
            timing = mean_ms[-1] / mean_ms[min(1, len(mean_ms) - 1)]
            verdict = "GROWS" if growth > 2 or timing > 2 else "flat"
            print(
                f"{shape:18} largest step x{growth:.1f}, mean step time x{timing:.1f} "
                f"from N={sizes[0]} to N={sizes[len(largest) - 1]}: {verdict}"
            )
    print(f"generated mdtests: {directory}")


if __name__ == "__main__":
    main()
