# An unsupported specification comparison names its operand types

```c filename=probe.c
int probe(int *p) { return 0; }
```

```click
verifying "probe.c";
int32 probe(int32* p) {
    ensures result == 0;
} by {
    have p == 7;
}
```

```expect
fail: cannot compare `int32*` and `int32` with `==`
```
