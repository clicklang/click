# A failed `auto` reports an inner `normalize` miss

Soundness: not soundness. Only the diagnostic is wrong; no verdict changes.

When `have P by auto;` fails, the diagnostic reports the last internal
search step that failed, not that `auto` could not prove `P`. The message
names a tactic the proof never wrote and a goal the reader never stated, so
it reports a cause that is not the cause.

Reproduced on master `da7834d2`. In
`examples/rust-chunks-exact/chunks.click`, replace the proof of the `have`
at line 64 with `by auto;`:

```click
have iter_remaining <= (bytes.len() - bytes.len() % 4u64) by auto;
```

`click verify chunks.click:64:13` fails with:

```
proof error:
  `normalize` goal did not normalize to true

tactic@64:
  have iter_remaining <= (bytes.len() - bytes.len() % 4u64) by auto;
goal: integer-condition((machine-integer<UInt64>(bytes.len())-machine-integer<UInt64>(uint64((bytes.len()%4u64)))) >= -2147483648) is true
```

The goal shown is the `int32` lower bound `auto`'s definedness search tried
for the `uint64` difference `bytes.len() - bytes.len() % 4u64`, several
searches below the stated `have`. It fails the same way with
`CLICK_DISABLE_TACTIC_BUDGETS=1`, so this is not a budget report. When
`auto` does run out of its tactic budget on a nearby site, the same
`normalize` message has also appeared in place of the budget report.

Intended regression: an mdtest with a `uint64` fact `auto` cannot prove,
whose search reaches the definedness solver, expecting a failure that names
`auto` and the stated proposition.

Acceptance:

- A failed `have P by auto;` says that `auto` could not prove `P` as
  written, and may then list bounded detail about what it tried. It does not
  lead with an internal step's error or an internal subgoal.
- A failure caused by an exhausted tactic budget says so, as other budget
  failures do.
