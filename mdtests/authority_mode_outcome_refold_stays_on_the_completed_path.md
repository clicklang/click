# An outcome refold of an ordinary family stays on the completed path in authority mode

After `execute()`, `identity` unfolds, refolds and unfolds again the
`marker(x)` it owns. Under authority semantics each outcome unfold is
retained as a checked exchange on the completed C path, but the refold was
not. The second unfold then started from the path's retained state, where
`marker(x)` was already unfolded, and was refused as "the rewritten composite
is absent from both resource representations". An outcome fold is now
retained too wherever the path's execution is complete.

This is reduced from the library scaling test
`outcome_haves_and_resource_folds_do_not_reimport_ambient_facts`.

```c filename=identity.c
int32 identity(int32 x) { return x; }
```

```click
resource marker(x: int32) { fact x == x; }
verifying "identity.c";
int32 identity(int32 x) {
    owns marker(x);
    ensures result == x;
} by {
    execute();
    unfold(marker(x));
    fold(marker(x));
    unfold(marker(x));
    fold(marker(x));
    simp();
}
```

```expect
pass
```
