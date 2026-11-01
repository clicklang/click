# Rust refusals inside macro expansions cite another file's line

Soundness: not soundness. Only the location in a refusal is wrong; no claim's
verdict changes.

A Rust import refusal reports `FILE:LINE in FUNCTION`, where `LINE` comes from
the span of the refused local, statement or terminator. When that item comes
from a standard-library macro, its span lies in the macro's own source (for
example `core/src/macros/mod.rs`), but the refusal still names the selected
source file with that other file's line number. The location then points past
the end of the user's file, or at an unrelated line.

## Reproduction

`click.project.json`:

```json
{"units": {"q": {"language": "rust", "sources": {"q.rs": {}}}}}
```

`q.rs`, four lines:

```rust
pub fn q(x: u32, y: u32) -> u32 {
    assert_eq!(x, y);
    x
}
```

`click import lock .` refuses with:

```text
click: unit `q`: q.rs:45 in q: Rust frontend does not support type `(&u32, &u32)` (raw pointers and general generics remain later work)
```

The refusal itself is expected (`assert_eq!` compares through a tuple of
references, which the frontend does not admit), but `q.rs` has four lines; 45
is a line of the `assert_eq!` definition. Before panics were admitted,
`assert!(x > 3)` on line 1 of a one-line file was refused at `p.rs:61`, and
`unreachable!()` at `p.rs:90`, the same way.

The location is built in `src/languages/rust/charon.rs` from
`span.data().beg.line` (for example the local-declaration loop's
`local.span.data().beg.line`), without checking that the span's file is the
selected source.

## Acceptance

- A refusal whose span lies in another file names a location in the selected
  source: the macro call site (Charon's `Span` records the call site in `data`
  and the macro's code in `generated_from_span`; whichever holds the user's
  file), or, failing that, the enclosing function's line.
- No refusal reports a line of a file other than the one it names.
- A regression imports the reproduction above and checks that the refusal
  cites `q.rs:2`, or at least a line no greater than 4.
