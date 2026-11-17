# Predicates

A predicate gives a name to a proposition.

For example:

<!-- verified-example: mdtests/compare_swap2_sorted_predicate.md -->
```click
predicate sorted_pair(p: int32[2]) {
    p[0] <= p[1]
}
```

Then a contract can use:

<!-- verified-example: mdtests/compare_swap2_sorted_predicate.md -->
```click
ensures sorted: sorted_pair(p) by {
    unfold(sorted_pair(p));
}
```

## Predicates are opaque

Predicate calls are not unfolded automatically. Click can reuse an exact
predicate fact, but it does not normally look inside a predicate unless the
proof says:

<!-- verified-example: mdtests/compare_swap2_sorted_predicate.md -->
```click
unfold(sorted_pair(p));
```

This opacity is useful. It lets predicates act as stable abstraction boundaries
instead of being expanded everywhere.

`unfold(sorted_pair(p))` selects that application at the current state. It
adds the definition equivalence, exposes the body when the application is
available, and replaces matching occurrences in the current goal. Other
applications and later goals stay opaque until explicitly opened.

## Predicates in requirements

Predicates can package preconditions:

<!-- verified-example: mdtests/predicate_packages_a_precondition.md -->
```click
predicate has_zero(p: int32[], n: int32) {
    (0..n).any(|k| { p[k] == 0 })
}

int32 find_zero(int32 p[], int32 n) {
    requires viewable(p[0..n]);
    requires has_zero(p, n);
    ...
}
```

If a proof needs the body of `has_zero`, unfold it and then use the resulting
facts. An available existential body can be opened with `obtain (...)`.

## Bodies read only their parameters

A predicate body may name its parameters, its own bindings, pure functions
and other predicates. It may not read a C object by name, whether a
file-scope variable by its bare name or any object by its qualified
`unit::name` form. A predicate fact is keyed on its arguments, so a body
reading `counter` would make `counter_is(5)` the same fact before and after a
store to `counter`. Pass the value as an argument instead, as
[pure functions](pure-functions.md#bodies-read-only-their-parameters) do:

<!-- verified-example: mdtests/a_pure_function_takes_a_global_value_as_an_argument.md -->
```click
predicate counter_is(c: int32, v: int32) {
    c == v
}
```

## When to define A predicate

Use a predicate when:

- a memory-reading precondition would otherwise be awkward,
- several contracts need the same concept,
- a loop invariant should name a larger property,
- or a proof should hide a complex proposition behind a stable name.

Avoid defining a predicate just to rename a one-line scalar fact unless the name
clarifies the proof.
