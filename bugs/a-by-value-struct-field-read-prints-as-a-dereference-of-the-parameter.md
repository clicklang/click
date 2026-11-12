# A by-value struct field read prints as a dereference of the parameter

Soundness: not soundness. The claim is refused correctly; only the text of
the refusal is wrong.

A diagnostic that renders the evaluated value of a by-value struct
parameter's field prints it as `*name`, a dereference of the struct value.
That is not Click or C: a struct value has no pointee. The value is the
field, and the report should spell it as the proof would, `old(input.value)`.

Invariant: a diagnostic spells a value the way a proof can write it
(`docs/internals/spellability.md`).

## Reproduction

`mdtests/aggregate_parameter_alias_mutation.md`, on master after
clicklang/click#2630:

```c filename=parameter_alias_mutation.c
struct packet { int32 value; };
int32 change(struct packet input) {
    int32* alias = &input.value;
    *alias = 5;
    return 0;
}
```

```click
verifying "parameter_alias_mutation.c";
int32 change(struct packet input) {
    ensures input.value == 5;
}
```

The claim is false and is refused, with:

```text
unclosed goal: input->value == 5; left side evaluated to old(*input), right side evaluated to 5
goal: old(*input) == 5
```

The mdtest's `expect` block pins `old(*input)` so the gate stays green; that
expectation is the wrong text and changes with the fix.

Before clicklang/click#2630 the same report said
`old(the caller's input.value)`, which was not syntax either. That wording
came from `registered_aggregate_argument_source` in
`describe_pointer` (`src/surface/diagnostics.rs`), which no longer applies
to a function's own proof, where the parameter's object is the input.

## Where it comes from

Not found. The rendered sides are built in
`src/surface/proof/driver/claims.rs` ("left side evaluated to") through
`render_c_value_labeled` and `Renderer::load_place`
(`src/surface/proof_diagnostics/render/surface.rs`). `load_place` keeps only
naming-table bases whose pointee type matches the load kind, which drops a
by-value struct parameter (its base is typed as bytes), and then falls back
to the address spelling plus `dereference`. Letting struct-value parameters
through that filter and selecting members with `.` in
`describe_parameter_struct_member` did not change the output, so another
path or naming table is involved.

## Acceptance criteria

- The reproduction's refusal reads `left side evaluated to
  old(input.value)` and `goal: old(input.value) == 5`.
- A field at a nonzero offset and a field of a nested struct print as
  `old(p.b)` and `old(p.inner.x)`.
- `mdtests/aggregate_parameter_alias_mutation.md` expects the corrected text.
