# `do { ... } while (0)` over a parameter or its memory fails with an internal evidence error

## Violated invariant

`do S while (0)` runs `S` once. `mdtests/c_do_while.md` verifies
`do_while_runs_once` with `auto` and no loop annotation, and says such
constant-bound loops are executed to their exit. That holds only when the
body touches locals declared in the function. When the body assigns a
parameter or stores through a pointer parameter, `auto`, `execute()`, and
`step()` all fail, and the message names no construct the user wrote:

```text
`execute` recorded condition evidence the proof object rejected
condition evidence was recorded with no source statement remaining
```

Reproduced on 2026-10-02 at `3390e37a1` and with a binary built from
`b3ab98334`. Each of these fails that way:

```c
int f(int v) { do { v = v + 0; } while (0); return v; }
/* int32 f(int32 v) { ensures result == v by auto; } */

int g(int *p) { do { *p = 3; } while (0); return *p; }
/* int32 g(int32* p) { owns p[0..1]; ensures result == 3 by auto; } */
```

The same function verifies when the loop is summarized
(`loop { decreases v; invariant v == 1; } step(); simp();` under
`requires v == 1`), and this variant, which copies the parameter into a local
first, verifies with `auto`:

```c
int h(int v) { int w = v; do { w = w + 0; } while (0); return w; }
```

This matters beyond the diagnostic. The Linux kernel wraps statement macros
in `do { ... } while (0)`: every `WRITE_ONCE`, `rcu_assign_pointer`, and
`compiletime_assert` in the pinned `lib/rbtree.c` translation unit expands to
one, over parameters and their memory. A proof of the imported unit would
need a loop annotation at each of them.

## Intended regression

An mdtest with `f` and `g` above and `ensures ... by auto`, expecting `pass`,
plus one where the body holds an `if` (`do { if (v == 7) v = 3; } while (0);`
under `requires v == 1`).

## Acceptance criteria

- `do S while (0)` verifies without a loop annotation whenever `S` followed
  by the rest of the function would, including when `S` assigns a parameter
  or stores through one, and when it contains `break` or `continue`.
- If some shape must still be refused, the diagnostic names the loop and says
  what annotation is needed; it does not report rejected condition evidence.
- `click expand` on such a proof produces a sidecar that re-verifies.
