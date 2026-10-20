# An inline `match` over a held resource's field does not refine itself

Soundness: incomplete. An implementation whose contract states exactly its
interface's clause is refused; nothing false is accepted.

The refinement check that compares a Rust trait implementation's contract
with its interface (and a function's contract with a named contract) proves
each target `ensures` from the implementation's. When the clause is an
inline `match` whose scrutinee is an opaque value, a held resource's field,
the identical clause on both sides does not prove: the implementation is
refused as not refining its interface. The same `match` over a constructor,
`match Option<T>::Some(x) { ... }`, refines, and so does the clause written
through a spec function, `value_or(old(item(self)), fallback)`.

Reproduction: in `design/charon-trial/resource-state/slots.click`, replace
the trait's

```click
        ensures result == value_or(old(item(self)), fallback);
```

with

```click
        ensures result == (match old(item(self)) { Option::Some(v) => v, Option::None => fallback });
```

`click verify design/charon-trial/resource-state/slots.click` then reports

```text
`<resource_state::Slot as resource_state::Store<u32>>::take_or` does not refine the trait method interface `resource_state::Store<u32>::take_or`
```

although the implementation's contract is that clause, inherited. A clause
without `old`, `ensures x == (match item(self) { Option::Some(v) => v,
Option::None => x });` on `put`, is refused the same way. The refusal is in
`function_refines_named_contract_in_case`
(`src/kernel/functions/named_contract_refinement.rs`), at
`prove_contract_propositions` over the target's `ensures`, after the
implementation's were assumed.

## Acceptance criteria

- The inline-`match` variant above verifies, and the implementation still
  refines nothing a changed clause does not give.
- A regression keeps the inline-`match` form, for example a mutation case in
  `tests/rust_import/trait_objects.rs::charon_trait_functions_are_defined_from_a_held_resource`
  or an mdtest of a named contract whose `ensures` matches on a resource
  field.
