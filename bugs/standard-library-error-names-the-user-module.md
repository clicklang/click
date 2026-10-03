# An error in the standard library is reported against the user's module

## Violated invariant

A diagnostic names the file and line where the problem is. When
`stdlib/prelude.click` does not check, every verification fails with a
message that names the sidecar being verified and a line number that belongs
to the prelude:

```text
type error:
  while checking module `example.click`
  line 3, column 6
  unexpected character '`'
```

`example.click` has no such line. Nothing in the message says the prelude is
involved, so whoever edits the prelude is sent to the wrong file.

Reproduced on 2026-10-02 at `3390e37a1` plus local changes: insert the line
``// a `quoted` word`` as line 3 of `stdlib/prelude.click`, rebuild, and run
`click verify` on any sidecar. The same comment line in a sidecar is
rejected too, with `syntax error: example.click:2 unexpected character`, so
the backtick is not itself the defect; only the attribution is.

## Intended regression

A unit test that checks a module against a prelude source with a deliberate
error and asserts that the diagnostic names the prelude and its line, not the
entry module.

## Acceptance criteria

- An error in the standard library names `stdlib/prelude.click` (or the
  embedded prelude) and the line within it.
