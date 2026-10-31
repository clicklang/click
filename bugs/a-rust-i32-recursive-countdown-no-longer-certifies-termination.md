# A Rust i32 recursive countdown no longer certifies termination

Soundness: incomplete. A terminating recursion is refused; nothing false
verifies.

`decreases n` on an `int32` parameter uses the body analysis that requires
each self-call to pass `n - K` for a positive constant `K`. The C form passes
(`mdtests/c_decreases_recursive.md`). The Rust form now fails: the importer
passes the argument through a checked temporary (`__rust_mir_N` holding
`n - 1`), and the analysis does not see through it. The same function
verified on 2026-10-22; the `i64` version, which takes the expression-measure
path, still verifies.

## Reproduction

`r.rs`, a Rust unit:

```rust
pub fn countdown(n: i32) -> i32 {
    if n <= 0 {
        return 0;
    }
    countdown(n - 1)
}

pub fn countdown64(n: i64) -> i64 {
    if n <= 0 {
        return 0;
    }
    countdown64(n - 1)
}
```

```click
verifying "r.rs";

fn countdown(n: i32) -> i32 {
    decreases n;
    ensures result == 0i32;
}

fn countdown64(n: i64) -> i64 {
    decreases n;
    ensures result == 0i64;
}
```

```text
proof error:
  could not certify C termination
  recursive call to `countdown` must pass `n - K` for a positive constant K
```

`countdown64` verifies.

## Acceptance criteria

- `countdown` verifies as written.
- A Rust self-call that passes `n` unchanged is still refused.
- A Rust recursion regression beside the other Rust fixtures; the coverage
  page's Recursion row can then cite it.
