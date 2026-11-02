# Audit cannot locate a generic Rust function's claim

Soundness: not soundness. The claims verify; only the expansion audit of a
generic Rust function's claim fails, so its expansion goes unchecked.

`click audit` rewrites a claim's smart tactics into the sidecar and then
looks the claim up again in the rewritten source. For a generic Rust function
such as `fn option_values::wrap<T: Copy>(value: T) -> Option<T>`, the
rewritten sidecar no longer parses at the function: the import declares an
`extern fn` instance of the generic function, and the expansion's `by { ... }`
lands on it, which the parser refuses.

## Reproduction

From the repository root, on master at 1b2354330:

```console
click audit design/charon-trial/option-values/options.click
click audit design/charon-trial/result-values/results.click
```

Each fails one claim, `option_values::wrap.ensures_0` and
`result_values::same.ensures_0`:

```text
could not locate `__rust_q_I13_option_values_I4_wrap.ensures_0` in the rewritten sidecar:
options.click:49: external function contracts cannot carry proof or decreases clauses
```

The other claims of both fixtures pass. Both functions verify normally.

## Acceptance criteria

- `click audit` of both fixtures passes every claim, including the generic
  functions', and the rewritten sidecar keeps the generic function's proof on
  the generic declaration, not on an `extern fn` instance.
- Regression: an audit test over a generic Rust function's claim (either
  fixture's generic function suffices).
