# A member load observes the initialized literal after its scalar update

```c filename=example.c
struct pair { int left; int right; };
int answer(void) {
    int count = 0;
    int value = (struct pair){count++, 22}.left;
    return value + count;
}
```

```click
verifying "example.c";
int32 answer() { ensures result == 1; }
```

```expect
pass
```
