# A refused call-site assembly does not name the missing fact

Soundness: not soundness. The refusal is correct; its diagnostic is not
actionable.

When a call needs `views R(a)` and the caller holds the owned bytes but no
instance, the call assembles the instance and checks the body's facts
(`design/borrowed-c-strings.md`, section (d)). The design's diagnostic
promises "the unclosed fact, as a refused fold reports it". A failed fact
instead reports a planning refusal that names neither the fact nor the
assembly:

```text
`step()` could not verify C operation
stable-view the required loan backing or binding is missing refused during planning; selected resource `views cstr_at(bytes, 2u64)`
```

`mdtests/cstr_at_call_assembly_needs_the_terminator_fact.md` pins only the
tail `selected resource ...` of this message. A `fold` of the same instance
at the same point reports `requires an exact body fact` with the missing
fact and the available facts.

## Reproduction

`mdtests/cstr_readable_witness_stated_before_call.md` with its three `have`s
removed: after the local declaration, the entry facts about `bytes` are not
restated at the call, so assembly is refused.

```c filename=assemble.c
uint64 fixed_string_length(uint8 bytes[]) {
    uint64 length;
    length = strlen(bytes);
    return length;
}
```

```click
verifying "assemble.c";

uint64 fixed_string_length(uint8 bytes[]) {
    owns bytes[0..3];
    requires bytes[0] != '\0';
    requires bytes[1] != '\0';
    requires bytes[2] == '\0';
    ensures result == 2u64;
} by {
    execute_until(statement(1));
    step(strlen(bytes), { s: click::cstr::cstr_at(bytes, 2u64) });
    execute();
    simp();
}
```

## Acceptance

- The refusal names the call, the assembled instance, and the first body
  fact it could not establish, with the available facts, as a refused `fold`
  does.
- `mdtests/cstr_at_call_assembly_needs_the_terminator_fact.md` expects the
  named fact.
