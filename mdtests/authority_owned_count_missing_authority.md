```c filename=bound.c
void inspect(int32* p) {}
```
```click resource_semantics=authority
authorized resource token(p: int32*) {}
verifying "bound.c";
void inspect(int32* p) {
    owns token(p);
    ensures 1 <= count(token(p));
} by { execute(); simp(); }
```
```expect
fail: count(...) requires owning authority for that population
```
