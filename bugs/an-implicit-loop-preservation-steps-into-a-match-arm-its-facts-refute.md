# An implicit loop preservation steps into a match arm its facts refute

Soundness: sound. The defect refuses a valid proof; it never accepts a false
claim. The refused arm's facts already contain `false`, so nothing proved there
could be wrong.

## Violated invariant

A `loop` with no `preserve` script preserves its invariants by stepping the
body. A step that reaches an `if` or `match` on an enum value omits the arms
its facts refute, as a proof-level `if` does. Here it does not: the implicit
preservation enters the `Some` arm of a match on the `Option` that
`SliceIter::next` returned, although the `next` contract and the loop
invariant together say the result is `None`. The arm's premises list `false`.
The step then refuses the payload read
`byte = (__rust_mir_7 as Some).0` with "a field of `Option::Some` is read from
a value not known to be that variant", instead of omitting the infeasible arm.

## Reproduction

A Rust unit with `"iterators": "library"`:

```json
{"units": {"sum": {"language": "rust", "iterators": "library", "sources": {"sum.rs": {}}}}}
```

`sum.rs`, the source of `examples/rust-iter-references`:

```rust
pub fn sum(bytes: &[u8]) -> i32 {
    let mut total = 0i32;
    for byte in bytes.iter() {
        total += *byte as i32;
    }
    total
}
```

`first.click`:

```text
import click::rust::slice;
import click::rust::slice_iter;
verifying "sum.rs";
fn sum(bytes: &[u8]) -> i32 {
    requires bytes.len() == 0u64;
    ensures result == 0;
} by {
    step_until(loop(0));
    have loop(0).iter.len() == 0u64;
    loop {
        decreases iter.len();
        invariant iter.len() == 0u64;
        invariant total == 0;
    }
}
```

`click verify first.click` fails at the `loop` tactic's preservation of the
invariants through the body:

```text
`step()` could not verify C operation
a field of `Option::Some` is read from a value not known to be that variant
C operation
byte = (__rust_mir_7 as Some).0
```

`click verify --trace-proof sum first.click` shows the `next` call adding
`value A:Option = Option::None` (from `iter.len() == 0`), then
`steps through: if (__rust_mir_7 is Some)` continuing into the `Some` arm;
the failed check's available premises include `false`.

A written `preserve` script that splits on `0u64 < iter.len()` and, in the
empty arm, states `have iter.len() == 0u64;` before stepping through the call
and the test does verify (`examples/rust-iterators/sum.click`).

## Acceptance criteria

- The reproduction verifies: the implicit preservation omits the `Some` arm
  whose facts refute it, and the empty-input loop needs no `preserve` script.
- A regression with this source and proof sits beside the other Rust iterator
  tests in `tests/rust_import.rs`.
- An arm that the facts do not refute is still entered and its payload read
  still checked.
