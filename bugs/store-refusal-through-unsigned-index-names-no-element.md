# Some refused accesses name no source element

## Violated invariant

A refusal must name what the user wrote, in source terms. A store or load
through an index of any integer type is named as its element
(`owns values[x..(x + 1)]`), and unsigned orders are spelled as unsigned
comparisons. Some other accesses still print the placeholder
`the pointer value at this program point` in place of a source spelling:

- a byte or narrower view inside a wider cell
  (`memory mutates only at [the pointer value at this program point (1 bytes)]`,
  `mdtests/a_byte_store_inside_a_wide_cell_is_not_framed.md`);
- a field of a struct array element past its ownership
  (`mdtests/a_heap_struct_array_element_field_store_past_its_ownership_is_refused.md`,
  `mdtests/struct_byte_array_resource_range_rejects_neighbor.md`);
- a load whose value is compared in a claim
  (`left side evaluated to load(the pointer value at this program point)`,
  `mdtests/aggregate_parameter_alias_mutation.md`,
  `mdtests/a_signed_ensures_read_is_not_an_unsigned_body_read.md`).

## Intended regression

For each shape above, tighten its mdtest to pin the source spelling of the
address (`(char *)q + 1`, `items[i].field`, `input->value`).

## Acceptance criteria

- No refusal of these shapes contains `the pointer value at this program
  point`.
- The spelling is the shortest one through the parameter or local the
  address belongs to, as `describe_pointer` already chooses for elements.
