# A claim that cannot lower is reported as another claim's unclosed goal

## Violated invariant

A refusal names the claim that failed and its cause. When a function has two
claims, one that holds and one that cannot be lowered (a `count(...)` over a
population the function holds no authority for), the implicit tail refuses
the function by naming the claim that holds: "`ensures member.serial ==
old(member.serial)` failed for `preserve.ensures_0` path 0: unclosed goal",
with both sides evaluated to the same value. The cause, "count(...) requires
owning authority for that population", is not reported. With the first claim
removed, the same function is refused with that cause.

Before `execute()` was removed, `} by { execute(); solve(); }` reported the
`count` refusal; the omitted proof, and a script that steps to exit first,
report the misleading message, on master as well.

## Reproduction

`helper.c`:

```c
void preserve(int32* pool) {}
int32 run() { int32 pool = 0; preserve(&pool); return 0; }
```

```click
authorized resource ticket(pool: int32*) { field serial: int32; }
verifying "helper.c";
void preserve(int32* pool) {
    owns authority(ticket(pool));
    owns member: ticket(pool);
    ensures member.serial == old(member.serial);
    ensures count(ticket(pool + 1)) >= 0;
}
```

`click verify` reports `preserve.ensures_0` as an unclosed goal whose two
sides evaluated to `<unnamed A>`. Deleting the `member.serial` claim makes the
refusal "count(...) requires owning authority for that population".

`mdtests/authority_named_import_other_anchor.md` and
`mdtests/authority_named_import_wildcard_other_anchor.md` keep only the
`count` claims, so they check the cause but not this report.

## Intended regression

An mdtest with the two claims above, expecting
`fail: count(...) requires owning authority for that population`.

## Acceptance criteria

- A function whose claims include one that cannot be lowered is refused with
  that claim and its lowering error, whatever claims precede it and whether
  the proof is omitted or ends in `step_until(function.exit)`.
- A claim that closes is never reported as an unclosed goal.
