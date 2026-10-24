# A read of a stored cell stays a read

After `a[i] = 5`, the Click expression `a[i]` lowers to the read of that cell
at the store's version, not to the stored value `5`: every read lowers to its
version name (`docs/internals/spellability.md`). So `a[i] == 5` is the store's
own fact, which `assumption` cites, rather than a goal that evaluates to
`true`. A rewrite that moves a read to an equal address keeps it a read: with
`i == j`, `rewrite(j == i)` turns the postcondition `a[j] == 5` into
`a[i] == 5`, the same fact. If `a[i]` lowered to `5`, that fact would have no
spelling and the rewritten goal could not be written.

```c filename=set.c
void set(int32* a, int32 i, int32 j) { a[i] = 5; }
```

```click
verifying "set.c";
void set(int32* a, int32 i, int32 j) {
    requires 0 <= i and i < 4;
    requires i == j;
    owns a[0..4];
    ensures a[j] == 5;
} by {
    execute();
    have a[i] == 5 by assumption();
    rewrite(j == i);
    assumption();
}
```

```expect
pass
```
