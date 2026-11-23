# Division by a shifted one still requires a valid count

```c filename=divide.c
uint32 divide(uint32 n, uint32 d) { return n / (1u << d); }
```

```click
verifying "divide.c";
uint32 divide(uint32 n, uint32 d) { requires d == 32u32; ensures true; }
```

```expect
fail: invalid shift
```
