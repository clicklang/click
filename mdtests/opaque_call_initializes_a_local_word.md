# A call initializes a local word at its exit

The contract for `fill` supplies initialized bytes, so C can read the word
without a contract equation giving its value. A call that writes only `y`
keeps that version. After a call that may overwrite `x`, the copy made
before the overwrite still equals the read named at the original exit.

```c filename=probe.c
void fill(int *p);
void touch(int *p);
void probe(void) {
    int x;
    int y = 0;
    fill(&x);
    touch(&y);
    int saved = x;
    touch(&x);
}
```

```click
verifying "probe.c";
extern void fill(int32* p) {
    consumes uninitialized(p[0..1]);
    produces p[0..1];
}
extern void touch(int32* p) {
    owns p[0..1];
}
void probe() {
    ensures true;
} by {
    step();
    step();
    step();
    step();
    step();
    have load<int32>(&x) == at(statement(2).call(0).exit, load<int32>(&x)) by close();
    step();
    step();
    have saved == at(statement(2).call(0).exit, load<int32>(&x)) by close();
    step();
    have saved == at(statement(2).call(0).exit, load<int32>(&x)) by close();
    step();
}
```

```expect
pass
```
