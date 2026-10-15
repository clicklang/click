# A mid-proof fold over a contract's view is refused

Soundness: incomplete. A documented fold is refused; no false acceptance is
known.

The tactic reference says folding a definition whose body views memory "makes
the head hold that borrow open until the head is unfolded or consumed", and
`mdtests/fold_cannot_view_memory_its_context_owns.md` directs a proof to
"receive the view as a borrow" instead of owning it. A function that receives
`views p[0..1]` by contract cannot fold `cell(p)`, whose body is
`views p[0..1];`, anywhere in its proof: the kernel rejects the checked
resource step with "resource rewrite changed more than a definitional
representation". The same fold verifies at a `produces` return, after
`execute()`.

The composite rewrite check in `src/kernel/proof/execution.rs` compares the
whole state before and after the fold except for resources, memory and
population fields. A fold that makes the head a dependency of the borrow
changes the loan ledger, which that comparison does not set aside; this is
the likely cause, not yet confirmed.

## Reproduction

Found while prototyping a borrowed C-string resource (`cstr_at` in
`library/cstr.click` on branch `cstrview`): a caller that borrows a string's
bytes has to fold `cstr_at` to lend it to a callee.

```c filename=probe.c
int32 first(int32 p[]) { return p[0]; }
```

```click
resource cell(p: int32*) {
    views p[0..1];
}

verifying "probe.c";

int32 first(int32 p[]) {
    views p[0..1];
    ensures result == p[0];
} by {
    fold(cell(p));
    unfold(cell(p));
    execute();
    simp();
}
```

Observed on master `5ad27faf`: `kernel rejected checked resource fold:
resource rewrite changed more than a definitional representation`. Folding
after a C step, then lending the folded head to a callee whose contract is
`views cell(p)`, fails the same way at the fold.

## Acceptance

- The reproduction verifies as written, kept as an mdtest, together with a
  fold that is lent to a `views cell(p)` callee and unfolded after the call.
- The kernel checks the ledger change the fold makes (the new dependency of
  the folded head on the borrow) against the fold's evidence, rather than
  excluding the ledger from the comparison.
- `mdtests/fold_cannot_view_memory_its_context_owns.md` still fails.
