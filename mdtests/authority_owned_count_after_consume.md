```c filename=consume.c
void consume(int32* p) {}
```
```click
authorized resource token(p: int32*) {}
verifying "consume.c";
void consume(int32* p) {
    owns authority(token(p));
    consumes token(p);
    ensures 0 <= count(token(p));
} by {
    have 0 < count(token(p)) by { solve() using { 1 <= count(token(p)); }; }
    unfold(token(p));
}
```
```expect
pass
```
