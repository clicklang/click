# A pure pointer equality grants no memory ownership

```c filename=read.c
int read_value(int *p) { return *p; }
```
```click
verifying "read.c";
function identity(p: int32*) -> int32* { p }
int32 read_value(int32* p) {
    requires identity(p) == p;
    ensures result == 0;
} by { execute(); }
```
```expect
fail: missing resource fact `views p[0]`
```
