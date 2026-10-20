# A scalar induction hypothesis is unknown inside `have` and `match`

Soundness: not soundness. Nothing false is accepted; a valid proof is
refused. After `induct(n) as ih`, `apply(ih(m))` works at the script's top
level and inside `if`, `both`, and `cases`, but inside a `have ... by` proof or
a `match` arm it fails with ``unknown theorem `ih` ``, so the hypothesis
cannot be used there at all.

The violated invariant: the local hypothesis `ih` introduced by scalar
`induct` is in scope for the whole rest of the script, including nested
proof blocks. The [scalar induction
reference](../docs/reference/tactics/index.md#scalar-induction) already lists
this refusal as a defect, not a boundary. The error also says "could not lower
theorem requirements", which describes nothing the user wrote.

A likely cause: the rewrite that turns `apply(ih(...))` into the hypothesis
instance descends only into `if`, `both`, and `cases` blocks, so a `have`
proof and `match` arms keep the raw `ih` name and the theorem lookup fails.
Algebraic `induct(xs) as ih { ... }` already resolves `ih` inside its arms.

```c filename=z.c
void unused() {}
```

```click
verifying "z.c";

function cd(n: int32) -> int32
    decreases n
{
    if n <= 0 { 0 } else { cd(n - 1) }
}

theorem t(n: int32) {
    requires n >= 0;
    ensures cd(n) == 0 by {
        induct(n) as ih;
        if n <= 0 {
            unfold(cd(n));
            normalize() using { n <= 0; };
        } else {
            have cd(n - 1) == 0 by apply(ih(n - 1));
            unfold(cd(n));
            rewrite(cd(n - 1) == 0);
            normalize();
        }
    }
}
```

`click verify` prints:

```text
proof error:
  could not lower theorem requirements
  unknown theorem `ih`

tactic@17:36:
  apply(ih(n - 1));
goal: cd(n - 1) == 0
refused by: `apply` (smart: it may miss; if the goal holds, prove it through smaller steps)
see: click docs apply
```

Replacing the `have` line with a bare `apply(ih(n - 1));` verifies. The block
form `have cd(n - 1) == 0 by { apply(ih(n - 1)) using { 0 <= n - 1; n - 1 < n; }; }`
fails the same way, reported against simple `apply`.

The same hypothesis inside a `match` arm:

```click
verifying "z.c";

spec enum Choice { A, B }

function cd(n: int32) -> int32
    decreases n
{
    if n <= 0 { 0 } else { cd(n - 1) }
}

theorem t(n: int32, c: Choice) {
    requires n >= 0;
    ensures cd(n) == 0 by {
        induct(n) as ih;
        if n <= 0 {
            unfold(cd(n));
            normalize() using { n <= 0; };
        } else {
            match c {
                Choice::A => { apply(ih(n - 1)); unfold(cd(n)); rewrite(cd(n - 1) == 0); normalize(); },
                Choice::B => { apply(ih(n - 1)); unfold(cd(n)); rewrite(cd(n - 1) == 0); normalize(); },
            }
        }
    }
}
```

prints the same ``unknown theorem `ih` `` error at `tactic@20:32`.

## Acceptance criteria

- Both reproductions verify, and expansion of each keeps `ih` inside the
  `have` and `match` arm.
- `apply(ih(m)) using { ... }` inside a `have` block also verifies with the
  same premises it needs at top level.
- `ih` inside a `have` nested in a `match` arm, and the reverse, resolves.
- Regressions keep both source patterns: `have ... by apply(ih(...))` in an
  `else` branch and `apply(ih(...))` in `match` arms over a non-inducted
  parameter.
- The defect note in the scalar induction reference is removed and the
  accepted nesting list names `have` and `match`.
