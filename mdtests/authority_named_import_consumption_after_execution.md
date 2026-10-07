# A unary named helper records exact occurrence consumption

The imported global count stays arbitrary. Each owned identity contributes one
checked death; equal arguments and fields do not merge the occurrences.

```c filename=named_retirement.c
void retire(int32* pool) {}
```

```click resource_semantics=authority
authorized resource ticket(pool: int32*) { field serial: int32; }
verifying "named_retirement.c";
void retire(int32* pool) {
    owns authority(ticket(pool));
    consumes left: ticket(pool);
    consumes right: ticket(pool);
    ensures count(ticket(pool)) == old(count(ticket(pool))) - 2;
} by { execute(); unfold(left); unfold(right); simp(); }
```

```expect
pass
```
