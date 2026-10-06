# A population count cannot supply missing caller custody

The caller owns one member while the global count is three. The call must
require the two declared input members from caller custody.

```c filename=quantity_exchange.c
void shrink(int32* counter) { *counter = *counter - 1; }
void lifecycle(int32* counter) { shrink(counter); }
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
    fold(member(counter));
    fold(control(counter));
    execute(); simp();
}
void lifecycle(int32* counter) {
    owns control(counter);
    owns member(counter);
    requires count(member(counter)) == 3;
} by { step(); execute(); simp(); }
```

```expect
fail: population call transfer refused: MissingMembers; declared 2 of member
```
