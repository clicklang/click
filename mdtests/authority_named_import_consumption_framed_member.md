# A unary named helper records exact occurrence consumption

The imported global count stays arbitrary. Each owned identity contributes one
checked death; equal arguments and fields do not merge the occurrences.

```c filename=named_retirement.c
void retire(int32* pool) {}
```

```click resource_semantics=authority
resource ticket(pool: int32*) { field serial: int32; }
verifying "named_retirement.c";
void retire(int32* pool) {
    owns authority(ticket(pool));
    consumes left: ticket(pool);
    owns right: ticket(pool);
    ensures right.serial == old(right.serial);
    ensures count(ticket(pool)) == old(count(ticket(pool))) - 1;
} by { unfold(left); execute(); simp(); }
```

```expect
pass
```
