# An introduced binder is not the identity a later quantifier binds

`intro()` on `forall (k: uint64)` used to keep the binder's own identity as
the witness whenever no fact named it. Binder identities were drawn from a
range shared with other lowered variables, so the next quantifier lowered in
that context, `forall (j: int32)`, bound the same identity the witness `k`
had free, and its range guards were assumed about it. A debug build stopped
with "integer width mismatch at an assumed condition: a variable used at
another width than before: expected a Bits64 carrier, found Bits32". A
quantifier's binder is now numbered by its height among nested quantifiers,
which no free variable shares, and opening it always renames the binder to a
fresh witness.

```c filename=an_introduced_binder_is_not_the_identity_a_later_quantifier_binds.c
void touch(unsigned char *dst) {
}
```

```click
verifying "an_introduced_binder_is_not_the_identity_a_later_quantifier_binds.c";

void touch(uint8* dst) {
    views dst[0..5];
} by {
    have forall (k: uint64) { k < 4u64 implies k < 5u64 } by {
        intro();
        intro();
        have forall (j: int32) { 0 <= j and j < 5 implies j < 6 } by {
            intro();
            intro();
            solve();
        }
        solve();
    }
}
```

```expect
pass
```
