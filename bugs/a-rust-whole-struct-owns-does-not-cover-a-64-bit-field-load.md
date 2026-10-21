# A Rust whole-struct `owns *x` does not cover a 64-bit field load

Soundness: incomplete. A valid program is refused; nothing false verifies.

A Rust sidecar that owns a whole struct through a reference, `owns *account`,
cannot read a 64-bit field of it, `usize`, `u64` or `i64`. The whole object
is seeded as `int32` cells, `size / 4` of them, and the Rust lowering reads
the field with a raw 8-byte load at its offset, which does not fit two 4-byte
cells: `a 8-byte load at `account` did not fit the cell's value`. Field-level
clauses, `owns account.balance; views account.id;`, verify. The same program
in C, `owns *a` with an `unsigned long` field, verifies.

## Reproduction

`more.rs`, a Rust unit:

```rust
pub struct Account {
    pub balance: usize,
    pub id: usize,
}

pub fn deposit(account: &mut Account, amount: usize) {
    account.balance += amount;
}
```

```click
verifying "more.rs";
fn deposit(account: &mut Account, amount: usize) {
    owns *account;
    requires account.balance <= 1000000usize;
    requires amount <= 1000000usize;
    ensures account.balance == old(account.balance) + amount;
    ensures account.id == old(account.id);
} by { execute(); simp(); }
```

```text
`execute()` could not verify C operation
a 8-byte load at `account` did not fit the cell's value
C operation
__rust_checked_0 = (load_uint64(account) as u64)
```

The trace shows `seed 4 Int32 cells at account, stride 4 bytes`.

## Findings

C++ attaches the record's layout to a record-reference parameter,
`C0Parameter::with_pointee_struct_layout` in `src/languages/cpp/interface.rs`;
the Rust lowering, `function_interface` in `src/languages/rust/lowering.rs`,
does not. Attaching it there makes the reproduction verify, but breaks the
generic stack's drop glue with an internal kernel error, `internal error
while applying an unfold: Click named an exposed cell inconsistently; it added
a cell no load reads`, in
`tests/rust_import.rs::charon_generic_stack_verifies_once_for_every_type` and
the generic container tests, whose records hold a field of an abstract type
`T`. That internal error is a defect of its own.

## Acceptance criteria

- The reproduction verifies as written, at `usize`, `u64` and `i64`.
- A claim that `account.id` changes is refused.
- The generic stack and container fixtures still verify.
- `design/charon-trial/integer-widths/widths.click`'s `deposit` states
  `owns *account` again.
