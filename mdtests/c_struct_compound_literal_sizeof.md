# Block-scope struct compound literal: sizeof

```c filename=example.c
struct pair { int left; int right; };
int answer(void) { int count = 0; return sizeof((struct pair){++count, 22}) + count; }
```

```click
verifying "example.c";
int32 answer() { ensures result == 8; }
```

```expect
pass
```
