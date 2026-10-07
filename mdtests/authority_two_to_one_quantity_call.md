# A checked quantity exchange preserves exact caller custody

The helper consumes two members and returns one. The caller starts with three,
observes the net decrement, and can spend exactly its two surviving members.

```c filename=quantity_exchange.c
void shrink(int32* counter) { *counter = *counter - 1; }
void lifecycle(int32* counter) { *counter = 3; shrink(counter); }
```

```click resource_semantics=authority
authorized resource member(counter: int32*) {}
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
    owns counter[0..1];
    owns authority(member(counter));
    requires count(member(counter)) == 0;
    ensures count(member(counter)) == 0;
} by {
    step();
    fold(3 of member(counter));
    fold(control(counter));
    step();
    have count(member(counter)) == 2 by simp;
    unfold(control(counter));
    unfold(2 of member(counter));
    execute(); simp();
}
```

```expect
pass
```
