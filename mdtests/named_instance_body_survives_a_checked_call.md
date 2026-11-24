# A named instance retains its body across a checked call

```c filename=named_return_body.c
void keep(int32* p) {}
int32 read_after(int32* p) { keep(p); return *p; }
```

```click
resource box(p: int32*) {
    field value: int32;
    owns *p;
    fact *p == value;
}
verifying "named_return_body.c";
void keep(int32* p) {
    owns held: box(p);
    ensures held.value == old(held.value);
}
int32 read_after(int32* p) {
    owns held: box(p);
    ensures result == old(held.value);
} by {
    step(keep, { held: held });
    unfold(held);
    step_until(function.exit);
    fold(held);
    close();
}
```

```expect
pass
```
