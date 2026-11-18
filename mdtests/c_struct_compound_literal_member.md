# Block-scope struct compound literal: member

```c filename=example.c
struct pair { int left; int right; };
int answer(void) { return (struct pair){20, 22}.right; }
```

```click
verifying "example.c";
int32 answer() { ensures result == 22; }
```

```expect
pass
```
