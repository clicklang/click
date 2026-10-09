# Named helper effects move explicit private storage between two populations

This uses explicit external member ownership. The recovered implicit-stack
storage refusal remains a separate unchanged-C control.

```c filename=transfer.c
void move(int32* source, int32* destination, int32* cell) {}
void invoke(int32* source, int32* destination, int32* cell) {
    move(source, destination, cell);
}
```

```click
authorized resource slot(pool: int32*, cell: int32*) { field label: int32; owns cell[0..1]; }
verifying "transfer.c";
void move(int32* source, int32* destination, int32* cell) {
    owns authority(slot(source, _));
    owns authority(slot(destination, _));
    consumes before: slot(source, cell);
    produces after: slot(destination, cell);
    requires source != destination;
    requires defined(count(slot(destination, _)) + 1);
    ensures after.label == old(before.label);
    ensures count(slot(source, _)) == old(count(slot(source, _))) - 1;
    ensures count(slot(destination, _)) == old(count(slot(destination, _))) + 1;
} by {
    unfold(before);
    let after = fold(slot(destination, cell), { label: old(before.label) });
    execute(); simp();
}
void invoke(int32* source, int32* destination, int32* cell) {
    owns authority(slot(source, _));
    owns authority(slot(destination, _));
    consumes before: slot(source, cell);
    owns retained: slot(destination, cell + 1);
    produces after: slot(destination, cell);
    requires source != destination;
    requires defined(count(slot(destination, _)) + 1);
    ensures after.label == old(before.label);
    ensures retained.label == old(retained.label);
    ensures count(slot(source, _)) == old(count(slot(source, _))) - 1;
    ensures count(slot(destination, _)) == old(count(slot(destination, _))) + 1;
} by {
    let { after: after } = step(move(source, destination, cell), { before: before });
    execute(); simp();
}
```

```expect
pass
```
