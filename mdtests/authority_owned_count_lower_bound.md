```c filename=bound.c
void inspect(int32* p) {}
void wrapper(int32* p) { inspect(p); }
```
```click
authorized resource token(p: int32*) {}
verifying "bound.c";
void inspect(int32* p) {
    owns authority(token(p));
    owns token(p);
    ensures 1 <= count(token(p));
}
void wrapper(int32* p) {
    owns authority(token(p));
    owns token(p);
    ensures 1 <= count(token(p));
}
```
```expect
pass
```
