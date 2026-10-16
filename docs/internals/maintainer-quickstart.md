# Quickstart

This page is for agents that need to make progress immediately.

## Run the project

From the repository root, run the same full gate as CI:

```console
scripts/check.sh
```

The gate checks formatting, documentation, unit tests, and proof fixtures. It
leaves nightly-only work to the nightly workflow. Use `cargo check` for a
targeted compile check and the fixture harness for focused proof work:

```console
cargo test --test mdtests
```

These focused commands do not replace the full gate. Prose-only changes can run
`scripts/check.sh --docs-only`; see [Testing Click](testing.md) for setup,
fixture selection, and named nightly tests.

## Mdtest format

Each `mdtests/*.md` file can contain prose, one or more C source blocks, one
Click block, and one expected-result block. A minimal file has these three
blocks:

<!-- verified-example: mdtests/mdtest_file_format.md -->
```c
int32 example() {
    return 0;
}
```

<!-- verified-example: mdtests/mdtest_file_format.md -->
```click
verifying "example.c";

int32 example() {
    ensures result == 0 by auto();
}
```

```expect
pass
```

In the file itself the C fence's info string also names the source,
`filename=example.c`, so the Click block's `verifying` clause can refer to it.
`mdtests/mdtest_file_format.md` is this example as a complete file.

Negative tests use:

```text
fail: expected diagnostic substring
```

Termination is part of the verdict, so a fixture whose summarized loop carries
no `decreases` clause is refused; see
[Testing Click](testing.md#termination-is-part-of-an-mdtests-verdict).

The harness is `tests/mdtests.rs`. It discovers fixtures under `mdtests/`;
ordinary runs skip the nightly list. Select a fixture by setting
`MDTEST_FILTER` to a filename fragment. Keep examples deterministic and
reasonably small.

## Minimal proof example

<!-- verified-example: mdtests/increment_requires_no_overflow.md -->
```c
int32 increment(int32 x) {
    return x + 1;
}
```

<!-- verified-example: mdtests/increment_requires_no_overflow.md -->
```click
verifying "increment.c";

int32 increment(int32 x) {
    requires x < 2147483647;
    ensures increments: result == x + 1 by auto();
}
```

The `requires` clause is needed because signed overflow is undefined behavior.
Click proves C code only when the requirements rule out undefined behavior and
the postcondition follows on every execution path.

## Common workflow

1. Find a nearby mdtest.
2. Copy the smallest relevant pattern.
3. Add the new behavior or failing case.
4. Run `cargo test --test mdtests`.
5. Implement parser/lowering/prover changes.
6. Update the relevant documentation.
7. Run `scripts/check.sh`, or `scripts/check.sh --docs-only` for prose-only
   changes.

## Where to look in source

- `src/languages/c/syntax.rs`: C parser and lowering.
- `src/surface.rs`: `.click` parser, validation, lowering, tactics, mdtest
  proof orchestration.
- `src/kernel/`: C semantic terms, propositions, assumptions, symbolic
  execution, and theorem-producing axioms.
- `library/`: the Click library modules, ordinary Click definitions.
