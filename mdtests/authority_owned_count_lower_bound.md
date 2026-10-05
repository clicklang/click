```c filename=bound.c
void inspect(int32* p) {}
void wrapper(int32* p) { inspect(p); }
```
```click resource_semantics=authority
resource token(p: int32*) {}
verifying "bound.c";
void inspect(int32* p) {
    owns authority(token(p));
    owns token(p);
    ensures 1 <= count(token(p));
} by { execute(); simp(); }
void wrapper(int32* p) {
    owns authority(token(p));
    owns token(p);
    ensures 1 <= count(token(p));
} by { execute(); simp(); }
```
```expect
pass
```
