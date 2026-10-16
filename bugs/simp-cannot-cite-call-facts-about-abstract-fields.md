# Simp cannot cite a callee's `ensures` about an abstract resource's fields

Soundness: incomplete. Click refuses true claims, and accepts nothing false.
A callee's postcondition about an abstract resource's model field is a
kernel fact at the caller. But `simp` uses that fact only for a goal that is
the identical proposition, so any arithmetic step through it is refused.

A field-bearing abstract resource (`abstract resource obj(p: int32*) { field
size: int32; }`, see `docs/reference/language/index.md`) is the object state
of Rust trait objects and C++ polymorphic classes. Their mutable receivers
change it through calls. Call-introduced facts should support arithmetic as
plain memory does: after `grow(s, 1)` with `ensures self[0] == old(self[0]) +
delta`, a caller proves `ensures s[0] - 1 == old(s[0])`. The same call on an
abstract field does not.

## Reproduction

```c
void grow(int32* self, int32 delta);
void bump(int32* s) { grow(s, 1); }
```

```click
abstract resource obj(p: int32*) {
    field size: int32;
}
extern void grow(int32* self, int32 delta) {
    owns o: obj(self);
    requires 0 <= delta and delta <= 100;
    requires 0 <= o.size and o.size <= 1000;
    ensures o.size == old(o.size) + delta;
}
void bump(int32* s) {
    owns o: obj(s);
    requires 0 <= o.size and o.size <= 500;
    ensures o.size - 1 == old(o.size);
} by { execute(); simp(); }
```

`click verify` refuses `bump.ensures_0`. The trace shows that the step adds
`o.size == old(o.size) + 1` to the facts, and the error's proof context lists
it among the pure facts. The obligation still fails, and the "available
premises" list shows only the `requires`. All of these are refused as well:
- `ensures o.size == old(o.size) + 1`, stated after a second `grow`, when
  the claim is `+ 2`;
- `ensures o.size <= 502`;
- a second `grow` whose precondition needs the first call's result; this
  surfaces as "`execute()` is missing prerequisite".

`ensures o.size == old(o.size) + 1`, the callee's postcondition word for
word, verifies: `simp` closes it by assumption.

The memory analogue has a narrower form of the same gap. One `grow` on
`owns self[0..1]` supports `ensures s[0] - 1 == old(s[0])`, but two calls
refuse `ensures s[0] - 2 == old(s[0])`. The intermediate value is only
readable at the second call's entry.

## Cause, as far as traced

`simp`'s arithmetic routes cite a premise only through its recorded or
synthesized source spelling (`available_surface_fact` in
`src/surface/proof/smart_closures.rs`). `synthesize_surface_proposition` in
`src/surface/proof/surface_synthesis.rs` has no spelling for a scalar
model-field variable; it spells algebraic ones only. Separately, the
statement-step recorder in
`src/surface/proof/proof_object/execution_statements.rs` skips any spelling
that contains `old(...)`, because at a call successor it would name the
callee's entry.

A trial patch did two things:
- spelled scalar field variables as `o.size`, `at(statement(k).entry,
  o.size)` or `old(o.size)`;
- recorded the snapshot-qualified spelling.

It produced spellings such as `o.size == (at(statement(1).entry, o.size) +
1)`, but `simp` still did not close the goals, and `execute()` does not pass
through that recorder at all. The remaining gap is in how `simp`'s arithmetic
routes collect and cite equalities. It was not traced further.

## Acceptance criteria

- The reproduction verifies, as do its two-call form (`+ 2`), the bound form
  (`<= 502`), and the two-call memory form, all with `execute(); simp();`.
- A second call's precondition that needs the first call's field result is
  discharged by `execute()`.
- The C++ mutable-receiver form verifies:
  - a non-`const` virtual `grow`;
  - with `ensures size(this) == old(size(this)) + delta`;
  - called twice by `Shape::grow_twice`;
  - with a caller that lends a `Square` and then calls `grow_twice`.
- The checked proofs expand and recheck, and simple checking stays within
  the step scaling tests.
