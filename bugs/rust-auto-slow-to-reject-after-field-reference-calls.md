# `auto` takes about 33 seconds to reject a false claim after field-reference calls

Soundness: not soundness. The false claim is rejected; only the time to
reject it is wrong.

The proof-failure triage rules expect a smart search to miss promptly. Here
`execute(); simp();` takes about 33 seconds to report that `auto` could not
prove a false postcondition. The program is four lines: one call through
`&mut` references to two struct fields, then one call whose argument is
another call's result. Each call alone fails in under three seconds (measured
on master `9b4218b5c`, debug build). The time goes into the `auto` search
behind `simp` (`checked outcome auto search did not retain a complete proof`).

Reproduction, a Rust crate unit `nongeneric_refs` with root
`nongeneric_refs::use_refs`:

```rust
pub fn peek(value: &u32) -> u32 {
    *value
}

pub fn put(slot: &mut u32, value: u32) {
    *slot = value;
}

pub fn exchange(left: &mut u32, right: &mut u32) {
    let held = *left;
    *left = *right;
    *right = held;
}

pub struct Slots {
    pub a: u32,
    pub b: u32,
}

pub fn use_refs(slots: &mut Slots) -> u32 {
    exchange(&mut slots.a, &mut slots.b);
    put(&mut slots.a, peek(&slots.b));
    slots.a
}
```

```click
verifying "refs.rs";

fn nongeneric_refs::peek(value: &u32) -> u32 {
    views *value;
    ensures result == *value;
} by { execute(); simp(); }

fn nongeneric_refs::put(slot: &mut u32, value: u32) {
    owns *slot;
    ensures *slot == value;
} by { execute(); simp(); }

fn nongeneric_refs::exchange(left: &mut u32, right: &mut u32) {
    owns *left;
    owns *right;
    ensures *left == old(*right);
    ensures *right == old(*left);
} by { execute(); simp(); }

// False: the result is old(slots.a).
fn nongeneric_refs::use_refs(slots: &mut nongeneric_refs::Slots) -> u32 {
    owns slots.a;
    owns slots.b;
    ensures result == old(slots.b);
    ensures slots.b == old(slots.a);
} by { execute(); simp(); }
```

With `ensures result == old(slots.a);`, the true claim, the sidecar verifies
in about a second. The generic version of the same program,
`design/charon-trial/generic-refs` with `exchange<T: Copy>`, `put` and `peek`
over `&T` and `&mut T`, takes the same time (about 35 seconds) to reject the
same false claim.

Variants measured with the same sidecar, trimmed to the functions each calls:

| `use_refs` body | result |
| --- | --- |
| `exchange(&mut slots.a, &mut slots.b); slots.a` | verifies (claim is true), 0.6 s |
| `put(&mut slots.a, peek(&slots.b)); slots.a` | rejected, 2.6 s |
| `put(&mut slots.a, slots.b); slots.a` | rejected, 1.0 s |
| `slots.a = slots.b; slots.a` | rejected, 0.3 s |
| both calls, as above | rejected, 33 s |

Acceptance criteria:

- The reproduction above is rejected promptly, within a few seconds in a
  debug build, still naming `nongeneric_refs::use_refs.ensures_0`.
- A regression test keeps the original four-line `use_refs` body and checks
  both outcomes: the false claim is rejected within the bound, and the true
  claim verifies.
- A focused trace of the failing search shows where the time goes, and the fix
  removes that cost rather than lowering a search limit.
