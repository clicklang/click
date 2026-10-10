# A caller's predicate requirement does not reach a call in a `return` or through a copy

## Violated invariant

Equivalent C forms verify alike. A caller that requires `cstr_readable(bytes)`
discharges `strlen`'s precondition for `n = strlen(bytes); return n;`, but
not for `return strlen(bytes);` or for `uint8* p; p = bytes; return
strlen(p);`, although each passes the same pointer with no intervening store.

## Reproduction

```c
int32 g(uint8 bytes[]) { return strlen(bytes); }
int32 h(uint8 bytes[]) { uint8* p; p = bytes; return strlen(p); }
```

```click
int32 g(uint8 bytes[]) {
    requires cstr_readable(bytes);
    ensures bytes[result] == '\0';
} by { execute(); simp(); }
```

Both fail with "`execute()` is missing prerequisite (strlen precondition) /
fact has no exact Click spelling at this frontier".

`cstr_readable` is transparent, so the kernel requirement is its unfolded
existential over the current memory, which never matches the caller's entry
fact exactly. The only route that discharges it is the source-backed caller
fallback `source_backed_direct_caller_requirement`
(`src/surface/proof/smart_closures.rs`). That fallback needs the unresolved
requirement to carry its call site, and the argument to name a caller
parameter, directly or through an identity cast:

- for `return strlen(bytes)` the requirement arrives with no call site, so
  the fallback is never consulted;
- for `strlen(p)` the argument is a local holding the parameter's value.

## Intended regression

An mdtest with `g` and `h` above, plus `size_t n = strlen(s); return n;` for a
`const char *s` caller, verifying with `execute(); simp();`. A version without
the caller requirement must still be refused for the missing precondition.

## Acceptance criteria

- A return-statement call carries its call site to the requirement fallback,
  or the kernel discharges a transparent predicate requirement whose unfolded
  form matches a caller fact up to the snapshot change of effect-free steps.
- A local copy of a parameter, with no store to the pointed-to storage in
  between, reaches the caller requirement the parameter has.
- Neither route admits a requirement the caller did not state.
