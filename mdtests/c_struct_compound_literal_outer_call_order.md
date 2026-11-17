# A call in an initializer cannot fix an outer operand's evaluation order

```c filename=example.c
struct pair { int left; int right; };
int g;
int set(void) { g = 1; return 0; }
int answer(void) { return (struct pair){set(), 22}.left + g; }
```

```click
verifying "example.c";
int32 set() { owns g; ensures g == 1; ensures result == 0; }
int32 answer() { owns g; requires g == 0; ensures result == 1; }
```

```expect
fail: requires an explicit prerequisite proof (the call leaves `g`
```
