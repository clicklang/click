# Pure-theorem diagnostics print parameters as `<unnamed A>`

Soundness: not soundness. Nothing is accepted that should not be; every
reproduction below is correctly refused. The defect is in the report: the
proposition a refusal names prints the theorem's parameters, introduced
binders, and `match` pattern bindings as `<unnamed A>`, `<unnamed B>`, ...,
so the reader cannot tell which variable the refused claim is about. In the
`transport` case two different claims print identically.

The violated invariant: a diagnostic prints a proposition in source spelling,
with every variable under the name the script uses for it, as the `goal:` line
of the same error already does (it prints `b == 1`, `f(x) == 0`,
`tot(lo, hi) == 0`). The affected text is the refusal's own detail lines
(premise or source/target propositions) and, after `intro()` or `unfold`, the
`goal:` line itself.

Each reproduction uses the same C file and fails with exit status 1.

```c filename=z.c
void unused() {}
```

## `transport using`: source and target print the same

```click
verifying "z.c";

theorem t(a: int32, b: int32) {
    requires a == 1;
    ensures b == 1 by {
        transport(a == 1, b == 1) using { a == 1; };
    }
}
```

```text
proof error:
  `transport using` target does not follow from the source fact and the listed premises
  source
  <unnamed A> == 1
  target
  <unnamed A> == 1
```

The source is `a == 1` and the target `b == 1`. The same placeholder appears in
"`transport using` requires a source derivable from its explicit facts" when
the source is not listed.

## `instantiate ... using`: the missing premise

```click
verifying "z.c";

function f(a: int32) -> int32 { a }

theorem t(x: int32, n: int32) {
    requires forall (k: int32) { 0 <= k and k < n implies f(k) == 0 };
    requires 0 <= x;
    requires x < n;
    ensures f(x) == 0 by {
        instantiate(forall (k: int32) { 0 <= k and k < n implies f(k) == 0 }, x) using { 0 <= x; };
    }
}
```

```text
proof error:
  `instantiate` failed
  instantiated premise `<unnamed A> < <unnamed B>` does not follow from the listed evidence
```

The premise is `x < n`.

## `peel ... using`: the missing premise

```click
verifying "z.c";

function tot(lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(k) })
}

theorem t(lo: int32, hi: int32) {
    ensures tot(lo, hi) == 0 by {
        peel(tot(lo, hi)) using { hi <= lo; };
    }
}
```

```text
proof error:
  `peel(tot(...)) using` requires an unavailable exact premise
  <unnamed A> <= <unnamed B>
```

## Induction premise

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
            apply(ih(n - 1)) using { n - 2 < n; };
        }
    }
}
```

```text
proof error:
  induction premise is not exactly available
  <unnamed A> - 2 < <unnamed A>
```

A conjunction premise such as `using { 0 <= n - 1 and n - 1 < n; }` prints
`0 <= <unnamed A> - 1 and <unnamed A> - 1 < <unnamed A>`.

## Goal after `intro()`

```click
verifying "z.c";

theorem t(n: int32) {
    ensures forall (a: int32) { forall (b: int32) { a == b } } by {
        intro();
        normalize();
    }
}
```

```text
proof error:
  `normalize` goal did not normalize to true

tactic@6:
  normalize();
goal: forall (k: int32) { <unnamed A> == k }
```

The introduced `a` prints as `<unnamed A>`, and the remaining binder `b` is
renamed `k`. With a single binder, `forall (a: int32) { a == n }`, the goal
prints `<unnamed A> == n`.

## `match` binding after `unfold`

```click
verifying "z.c";

spec enum Ctx { Top, Up(Ctx) }

function d(c: Ctx) -> Integer decreases c {
    match c { Ctx::Top => 0, Ctx::Up(u) => 1 + d(u) }
}

theorem t(c: Ctx) {
    ensures d(c) >= 0 by {
        unfold(d(c));
        contradiction(1 == 5);
    }
}
```

```text
goal: match c { Top => 0, Up => 1 + d(<unnamed A>) } >= 0
```

The arm's binding `u` is dropped from the pattern and its use prints as
`<unnamed A>`.

## Acceptance criteria

- Each reproduction above prints its propositions with the source names:
  `a == 1` and `b == 1`; `x < n`; the listed `hi <= lo`; `n - 2 < n`;
  `forall (b: int32) { a == b }`; `match c { Top => 0, Up(u) => 1 + d(u) }`.
- No pure-theorem diagnostic prints `<unnamed`. A regression asserts the
  absence for at least the `transport`, `instantiate`, `intro()`, and `match`
  cases.
- A bound variable keeps its source name unless that name would capture
  another variable in the printed proposition.
