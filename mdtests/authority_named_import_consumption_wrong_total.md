# A unary named helper records exact occurrence consumption

The imported global count stays arbitrary. Each owned identity contributes one
checked death; equal arguments and fields do not merge the occurrences.

```c filename=named_retirement.c
void retire(int32* pool) {}
```

```click
authorized resource ticket(pool: int32*) { field serial: int32; }
verifying "named_retirement.c";
void retire(int32* pool) {
    owns authority(ticket(pool));
    consumes left: ticket(pool);
    consumes right: ticket(pool);
    ensures count(ticket(pool)) == old(count(ticket(pool))) ;
} by { unfold(left); unfold(right); execute(); simp(); }
```

```expect
fail: search did not retain a complete proof
```
