# `open` of an owned `cstr_at` refuses its body

Soundness: incomplete. The refusal stops a proof that `unfold` and a
`views` open both accept; no false acceptance is known.

`open(R(a)) { ... }` temporarily replaces a held composite with one body
layer and folds it back at the end of the block
(`docs/reference/tactics/index.md`). For `cstr_at`, whose body owns its bytes
(`library/cstr.click`), it works on a viewed instance
(`mdtests/cstr_at_opens_and_lends_a_prefix_to_a_copy.md`), and `unfold` works
on an owned one (`mdtests/cstr_at_owner_rewrites_a_byte_and_refolds_the_same_length.md`).
`open` on an owned instance is refused at entry, before any C statement runs,
with a diagnostic that names `unfold` and an internal concept instead of the
body fact it could not support:

```text
`outer.contract` tactic 0
`unfold(cstr_at(src, n))` rejected dynamic body dependency
current body fact is covered by an unbound viewed memory occurrence
```

The message comes from `check_load` in `src/surface/proof/resources.rs`: a
body fact's cell is covered by a view occurrence with no loan dependency.
An owned instance has no loan, so the open path apparently lowers or checks
the owned body as if it were a borrowed view.

## Reproduction

```c filename=open_owned.c
uint64 outer(uint8 *src, uint64 n)
{
	return 0;
}
```

```click
import click::cstr;
verifying "open_owned.c";

uint64 outer(uint8* src, uint64 n) {
    owns cstr_at(src, n);
    requires 0u64 < n;
    ensures result == 0u64;
} by {
    open(cstr_at(src, n)) {
        execute();
    }
}
```

The same file with `views cstr_at(src, n);` verifies, and so does the owned
form with `unfold(cstr_at(src, n));` followed by an explicit refold.

## Acceptance

- The reproduction verifies as an mdtest (`expect pass`).
- An owned `open` whose block writes a byte and leaves a body fact unproved
  at the close names that fact, as a refused `fold` does ("requires an exact
  body fact ..."), and names the closing fold rather than `unfold`.
