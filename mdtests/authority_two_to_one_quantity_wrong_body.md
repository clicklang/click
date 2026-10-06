# A helper must establish its declared quantity effect

The helper produces two members while its contract declares one. Folding
the counter control must reject the false count equation.

```c filename=quantity_exchange.c
void shrink(int32* counter) { *counter = *counter - 1; }
void lifecycle() { int32 counter = 3; shrink(&counter); }
```

```click resource_semantics=authority
resource member(counter: int32*) {}
resource control(counter: int32*) {
    owns counter[0..1];
    owns authority(member(counter));
    fact counter[0] == count(member(counter));
}
verifying "quantity_exchange.c";
void shrink(int32* counter) {
    owns control(counter);
    consumes 2 of member(counter);
    produces member(counter);
    ensures count(member(counter)) == old(count(member(counter))) - 1;
} by {
    unfold(control(counter));
    unfold(2 of member(counter));
    step();
    fold(2 of member(counter));
    fold(control(counter));
    execute(); simp();
}
void lifecycle() { ensures 1 == 1; } by {
    step(); step();
    fold(authority(member(&counter)));
    fold(3 of member(&counter));
    fold(control(&counter));
    step();
    have count(member(&counter)) == 2 by simp;
    unfold(control(&counter));
    unfold(2 of member(&counter));
    unfold(authority(member(&counter)));
    execute(); simp();
}
```

```expect
fail: Requires counter[0] == count(member(counter))
```
