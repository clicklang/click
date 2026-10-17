# Refinement hints still bind produced resources as call inputs

Soundness: not soundness. The verifier's suggested theorem contains obsolete
`step` syntax, so following the hint causes a parser refusal rather than
checking the intended refinement.

The reproduction is the automatic refinement refusal from
`mdtests/model_pointer_callback_preserves_declared_types.md` before its explicit
`wrapped_is_callback` theorem is supplied. The hint prints:

```click
step(wrapped(p), { held: r });
```

`wrapped` produces `held`. This is rejected with “introduce it with
`let { held: name } = step(...)`”. The correct proof step is:

```click
let { held: r } = step(wrapped(p), {});
```

Acceptance criteria: generated theorem skeletons keep required instances in
the input map and introduce produced instances through output bindings. The
suggested source must parse and verify when the refinement itself is valid.
The explicit callback fixture demonstrates the corrected output pattern.
