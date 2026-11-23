# The zero arm cannot use the original divisor
```c filename=f.c
uint32 f(uint32 x, uint32 d) { return x / (d ? 1u : d); }
```
```click
verifying "f.c";
uint32 f(uint32 x, uint32 d) {  ensures true; }
```

```expect
fail: division by zero
```
