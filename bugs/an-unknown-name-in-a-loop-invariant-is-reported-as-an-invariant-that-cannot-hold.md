# An unknown name in a loop invariant is reported as an invariant that cannot hold

Soundness: not soundness. The invariant is refused, so nothing false
verifies; the defect is the diagnostic.

A name that resolves to nothing is reported as `unknown name` in a contract
clause, but not in a loop invariant. There it lowers to something the kernel
decides false at the loop's entry, so the refusal reads `this invariant cannot
hold here`, which points the author at their arithmetic instead of their
spelling. Even `invariant bogus == bogus;` is refused that way. This bites
Rust proofs in particular: an iterator's state names (`iter_start`,
`iter_cursor`) change to `__rust_mir_ID_...` when the source name is
ambiguous, as in nested loops, and the stale spelling gives no hint.

## Reproduction

`lp.c`:

```c
int lp(int n) {
    int i = 0;
    while (i < n) {
        i = i + 1;
    }
    return i;
}
```

```click
verifying "lp.c";

int32 lp(int32 n) {
    requires n >= 0;
    ensures result == n;
} by {
    step_until(loop(0));
    loop {
        decreases n - i;
        invariant bogus <= n;
        invariant 0 <= i and i <= n;
    }
}
```

```text
proof error:
  loop 0 invariant 0 entry
  this invariant cannot hold here
  a condition it owes is already decided false at this state
```

The same name in `ensures result == n or bogus == 3;` is a type error:
`unknown name `bogus` in `ensures ...``.

## Acceptance criteria

- The reproduction is a type error naming `bogus` and the invariant, as for an
  `ensures` clause, before any proof runs.
- A loop's `decreases`, `views`/`owns` entries and `preserve` body report an
  unknown name the same way.
- An mdtest pins the diagnostic.
