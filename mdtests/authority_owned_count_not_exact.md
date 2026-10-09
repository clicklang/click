```c filename=bound.c
void inspect(int32* p) {}
```
```click
authorized resource token(p: int32*) {}
verifying "bound.c";
void inspect(int32* p) {
    owns authority(token(p));
    owns token(p);
    ensures count(token(p)) == 1;
} by { execute(); simp(); }
```
```expect
fail: count(token(p)) == 1
```
