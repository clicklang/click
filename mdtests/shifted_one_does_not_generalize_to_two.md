# A valid count can shift the only set bit of two out of the word

```c filename=divide.c
uint32 divide(uint32 n, uint32 d) { return n / (2u << d); }
```

```click
verifying "divide.c";
uint32 divide(uint32 n, uint32 d) { requires d == 31u32; ensures true; }
```

```expect
fail: division by zero
```
