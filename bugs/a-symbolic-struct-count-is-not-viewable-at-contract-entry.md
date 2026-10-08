# A `viewable` range over a symbolic number of structs does not make its first struct readable at contract entry

## Violated invariant

A range on a struct pointer counts structs. `viewable(node[0..n])` with
`n >= 1` covers `node[0]`, so a clause that reads `node->left` to form a
resource argument has the access it needs. Entry evaluation must accept it,
as it accepts the same premise over a constant count.

## Reproduction

```c
struct node {
    struct node *left;
    int32 value;
};

void probe(struct node *node, int32 n) { }
```

```click
resource cell(node: struct node*) {
    owns node->left;
}

verifying "nested_dynamic_dependent_pair.c";

contract void NestedDynamicDependentPair(struct node* node, int32 n) {
    requires node != 0;
    requires n >= 1 and viewable(node[0..n]);
    requires n <= 2147483647;
    owns cell(node->left);
}
```

`click verify` reports

```
could not prepare named contract `NestedDynamicDependentPair`
could not evaluate `node->left` while checking `owns cell(node->left)`:
resource `cell` argument 0 produced runtime error: a required resource is
not available
```

With `viewable(node[0..1])` the contract is accepted.

## Cause

The parser lowers a range on a struct pointer to four-byte cells by
multiplying each bound by the struct's cell count
(`parse_current_contract_segments_inner` in `src/surface/parser.rs`), so the
premise is `viewable` over cells `[0 .. 4 * n)`. Entry evaluation finds cell 0
inside `[0 .. n)` from `n >= 1`, but does not derive `0 < 4 * n` from it.

Before ranges counted structs, this contract was written with `n` cells and
passed. `mdtests/contract_nested_dynamic_viewable_composite_argument.md` held
that form; it now names the field (`viewable(node->left)`).

A struct-array parameter (`struct item items[2]`) does not have this problem:
its range keeps the struct as the element width through lowering
(`contract_segment_element_width` in
`src/surface/lowering/resource_lowering.rs`). Giving a struct pointer's range
the same element width, in place of scaling its bounds, would remove the
multiplication.

## Intended regression

The reproduction above as an mdtest expecting `pass`, and a variant with
`n >= 0` expecting refusal.

## Acceptance

- The reproduction verifies.
- The `n >= 0` variant is refused: no struct is known to be covered.
- A range on a struct pointer reaches the kernel with the struct as its
  element width, with no multiplied bound.
