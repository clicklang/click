# Written closers miss a claim the implicit closer proves from a call's guarded postcondition

## Violated invariant

After execution, the implicit `auto` that ends a proof and a written `auto()`
are the same closer (`docs/reference/tactics/index.md`, "Goals after
execution"). A claim the implicit closer proves should also be provable by
writing `auto()`, and by the simple closers its expansion would print.

Today the implicit closer proves a claim from a callee's postcondition that
no written closer proves. The callee's `ensures result == x + 1` reaches the
caller as the guarded fact `x <= 2147483646 implies result == x + 1`. The
implicit closer matches the caller's identical claim in its guarded kernel
form. `auto()`, `simp()`, `assumption()` and `normalize()` focus the
unguarded goal `result == (x + 1)` and are refused.

## Reproduction

`t.c`:

```c
int helper(int x);
int caller(int x) { return helper(x); }
```

`t.click`:

```
verifying "t.c";
extern int32 helper(int32 x) { ensures result == x + 1; }
int32 caller(int32 x) {
    ensures result == x + 1 by { execute(); }
}
```

`click verify t.click` verifies. Writing `assumption();` or `normalize();`
after `execute();` is refused with "found no available fact" or "did not
prove the current goal `result == (x + 1)`". Writing `auto();` or `simp();`
verifies only because a written `simp`/`auto` that closes nothing is skipped
(`bugs/written-simp-that-closes-nothing-is-skipped.md`); `click expand`
drops it, and with that skip removed both are refused with "unclosed goal".
`mdtests/global_array_resource_element_types.md` (`ensures bytes[1] == 7 by
auto();`) passes the same way.

## Status

The written `simp`/`auto` now try a claim they could not close as its own
kernel claim goal, as the implicit closer does, so they close this claim.
While a written closer that closes nothing is still skipped
(`bugs/written-simp-that-closes-nothing-is-skipped.md`), no test can tell
the two apart. The regression lands with that refusal; delete this file then.

## Intended regression

An mdtest with the source above that verifies with no closer, with
`auto();`, and with `assumption();`, and whose `click expand` output
verifies.

## Acceptance criteria

- Written `auto()` closes every claim the implicit closer closes.
- `assumption()` closes a claim whose guarded kernel form is an available
  fact, as the implicit closer does.
- `click expand` of the implicit proof prints closers that verify.
