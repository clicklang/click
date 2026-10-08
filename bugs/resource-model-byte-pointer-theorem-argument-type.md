# Resource-model byte pointer loses its type at theorem application

## Violated invariant

A pointer extracted from a resource model declared `const uint8*` must keep
its element type when supplied to a theorem with a `const uint8*` parameter.
The current fixed-state array-reference capture instead reports `Int32`.
The theorem itself verifies; proving the same pointer association directly
with its selected definedness guard also verifies.

Reproduced on the Adler induction branch using the following unchanged C
and sidecar. `click verify model-argument.click` fails at the theorem application:

```
`apply` failed
theorem `bounded_pointer_association` parameter `base` expects UInt8 array elements, got Int32
```

## Small intended regression

`simple.c`:

```c
void keep(const uint8* p, int32 i) {}
```

`model-argument.click`:

```click
verifying "simple.c";
spec enum Link { Node(const uint8*) }
resource Cell(p: const uint8*, i: int32) {
 field model: Link;
 match model { Link::Node(q) => { owns p[0..i + 4]; fact q == p; }, }
}
theorem bounded_pointer_association(base: const uint8*, index: int32) {
 requires 0 <= index;
 requires index <= 22200;
 ensures (base + index) + 4 == base + (index + 4) by {
  have defined(index + 4) by { simp() using { 0 <= index; index <= 22200; } }
  normalize() using { defined(index + 4); }
 }
}
void keep(const uint8* p, int32 i) {
 requires 0 <= i;
 requires i <= 22200;
 owns h: Cell(p, i);
} by {
 match h.model {
  Link::Node(q) => {
   unfold(h);
   have (q + i) + 4 == q + (i + 4) by { apply(bounded_pointer_association(q, i)) using { 0 <= i; i <= 22200; } }
   let h = fold(Cell(p, i), { model: Link::Node(q) });
   execute(); simp();
  },
 }
}
```

The fallback in
`src/surface/proof/fixed_state_proofs/have_proofs.rs::evaluate_fixed_state_array_ref_through_kernel`
uses `CType::Int32` when `contract_array_ref_element_type` cannot recover the
model binding. Preserve the declared pointer type through the existing typed
capture and binding path; do not infer it from the destination theorem.

## Acceptance criteria

- This source and sidecar verify without changing the C, resource model,
  theorem signature, or pointer expression.
- Type information survives resource-model matching, pointer expressions,
  and applicable entry/label snapshots, with their original memory meaning.
- A genuinely incompatible pointer argument is rejected; recovering an
  element type grants no memory or allocation authority.
- Verification, profiling, expansion and audit agree on the repaired proof.
- Binding lookup work scales with the selected expression and required
  bindings, independently of unrelated environment entries.
