# A by-value aggregate parameter's incoming storage has no source name

## Violated invariant

A refusal must name what the user wrote, in source terms. An address reached
through a pointer parameter is spelled through it: an element (`values[x]`),
a struct member (`p->data[2]`, `p[i].y`), or a byte offset
(`(char *)q + 1`). One address still prints the placeholder
`the pointer value at this program point`: the storage a by-value aggregate
argument arrives in.

A parameter `struct packet input` is two objects. The callee's copy is a
local the naming tables call `input`. The value it was copied from lives at
an address the tables do not carry, so a claim that reads it prints

```
input->value == 5; left side evaluated to load(the pointer value at this program point), right side evaluated to 5
```

(`mdtests/aggregate_parameter_alias_mutation.md`,
`mdtests/an_uncertified_claim_is_spelled_in_source_terms.md`,
`mdtests/aggregate_parameter_pointee_expires.md`).

A second leftover is an address named inside another address's index. The
index is spelled without the naming tables, because naming a loaded index
describes the cell it was loaded from, which can be the address being
spelled. So a load nested in an index still prints the placeholder
(`viewable(base=node[((load(the pointer value at this program point) + 2) - …)], bytes=8)`,
`mdtests/contract_certification_reports_resource_error.md`), and an index a
local names prints as `…` (`owns p[…].y`).

## Intended regression

Tighten those three mdtests to pin a spelling that names the parameter and
says which object is meant, for example `the caller's input.value`.

## Acceptance criteria

- The function entry records, for each by-value aggregate parameter, the
  address its argument arrived at, so a diagnostic can name it.
- No refusal contains `the pointer value at this program point` for an
  address that belongs to a parameter.
