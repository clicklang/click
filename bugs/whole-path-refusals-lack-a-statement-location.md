# Whole-path refusals don't name a C statement

## Violated invariant

Every refusal about a C program should say where in the C it applies. PR #47
added `C statement at file:line` plus the source text to refusals of a single
step, but 16 kinds of failing output still have no location. They come from
the kernel's per-path outcome, which doesn't record which statement it was
on:

- `path N: undefined behavior` from whole-path execution;
- end-of-function leaks and unreleased mutex obligations;
- contract setup failures;
- callback theorems with no C body.

## Intended regression

Mdtests for a leak at a `return`, a mutex still held at the end of a function,
and whole-path undefined behaviour, each pinning `C statement at f.c:LINE` and
the statement text (the `return`, or the statement that caused the undefined
behaviour).

## Acceptance criteria

- Each per-path outcome carries the statement index it ended or failed at, as
  a diagnostics-only site (like PR #47's `C0Site`): it must not affect
  identity, interning, caching or work.
- The refusals listed above print the location and source text.
