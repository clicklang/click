# Callable parameter signature mismatch prints internal type ids

Soundness: not soundness. The mismatch is refused; only the diagnostic is
wrong.

Priority: P3.

A sidecar head whose callable parameter has a different signature from the
source's is refused with the kernel's interned type ids instead of the two
signatures:

```text
type error:
  signature mismatch for `function_pointers::apply` parameter 1 in `callback.rs`
  .click has FunctionPointer(2257) f, C has FunctionPointer(2163) f
```

The ids are internal and stable only within one run, so the reader cannot tell
what differs. The same message comes from a Rust `fn(...)` pointer, an
`impl Fn(...)` parameter, and an `<F: Fn(...)>` parameter, which share
`check_signature` in `src/surface/verification.rs`; a C function-pointer
parameter goes through the same check but was not reproduced. Its `describe_parameter_type` writes a
function-pointer `C0Type` as the variant and its id, and ignores the
parameter's `function_pointer_signature`, which holds the signature.

## Reproduction

In `design/charon-trial/function-pointers/callback.click`, change the head of
`function_pointers::apply` to `f: fn(u32) -> u32` and delete its
`requires Doubling(f);` (which otherwise reports the type first, correctly),
then run `click verify callback.click`.

## Acceptance criteria

- The message names both signatures in the source language's spelling, or at
  least as C types (`uint32 (*)(uint32)` against `int32 (*)(int32)`), as the
  named-contract type error already does.
- A regression checks the message for a Rust callable parameter.
