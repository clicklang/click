# A Rust `u8` remainder guard does not meet its sidecar reading

Soundness: not soundness. A true claim is refused; nothing false is accepted.

At `u8`, a sidecar fact and the importer's guard over the same expression are
spelled differently, and the verifier does not relate the two. A sidecar's
`x % 2u8 == 0u8` is recorded as `(x as i32) % 2 == 0`. The Rust body's
`x % 2 == 0` lowers to `(((x as u32) % 2u32 as u8) as u32) == 0u32`. With the
first as a precondition, the second is neither decided automatically nor
provable by explicit steps. The same function at `u32` verifies.

## Reproduction

`click.project.json`:

```json
{"units": {"q": {"language": "rust", "sources": {"q.rs": {}}}}}
```

`q.rs`:

```rust
pub fn parity(x: u8) -> u8 {
    if x % 2 == 0 {
        1
    } else {
        0
    }
}
```

`q.click`:

```click
verifying "q.rs";
fn parity(x: u8) -> u8 { requires x % 2u8 == 0u8; ensures result == 1u8; }
```

`click import lock .` then `click verify q.click` refuses:

```text
  `ensures result == 1u8` failed for `parity.ensures_0` path 0
  unclosed goal
  result == 1u8; left side evaluated to 0u8, right side evaluated to 1u8
  proof context
  case: [(((x as u32) % 2u32 as u8) as u32) != 0u32]
goal: false
```

The `else` path should be infeasible under the precondition. With `u32` in
place of `u8` in both files, the proof verifies.

The same gap blocks `assert!(x % 2 == 0)` on a `u8`. Its refusal reads
``could not show `(((x as u32) % 2u32 as u8) as u32) == 0u32` from the facts
`(x as i32) % 2 == 0`, `to_integer(((x as u32) % 2u32 as u8)) ==
to_integer((x as u32) % 2u32)` ``. Explicit steps do not help either: `have (x
as u32) % 2u32 == 0u32 by { solve(); }` is refused.

## Acceptance

- `parity` above verifies at `u8` with no proof, as it does at `u32`.
- The `assert!(x % 2 == 0)` form at `u8` verifies under
  `requires x % 2u8 == 0u8`.
- The regression keeps the `u8` remainder comparison as written. It covers
  `u16` too, which shares the `int` promotion.
