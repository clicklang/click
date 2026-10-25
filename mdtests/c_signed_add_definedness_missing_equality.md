```c filename=defined.c
int32 f(int32 x, int32 y, int32 z) { return y + z; }
```
```click
verifying "defined.c";
int32 f(int32 x, int32 y, int32 z) {
    requires defined(x + z);
    ensures result == y + z;
} by { execute(); solve(); }
```
```expect
fail: signed overflow
```
