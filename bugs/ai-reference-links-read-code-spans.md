# The AI-reference generator reads links inside code spans

Soundness: not soundness. A documentation build check refuses valid prose; no
verification result is affected.

Priority: P3.

`ai_reference::generate` in `tests/support/ai_reference.rs` rewrites and checks
every Markdown link in `docs/`, but it finds links in inline code spans too. A
code span is literal text in Markdown, so `[](int y)` inside backticks is not a
link. The check fails the `documentation::ai_reference_site_files_generate`
gate test with:

```text
docs/reference/cli/import.md: link int y does not resolve to a file under docs/
```

## Reproduction

Add a sentence to any page under `docs/`, for example
`docs/reference/cli/import.md`, that shows a C++ lambda in a code span:

```markdown
A lambda, `apply([](int y) noexcept { return y + y; }, x)`, is its address.
```

Then run `scripts/check.sh --docs-only`. The page currently writes
`[] (int y)`, with a space, to avoid the failure.

## Acceptance criteria

- Text inside inline code spans and fenced code blocks is not read as a link.
- A regression checks that a code span containing `[](x)` generates.
