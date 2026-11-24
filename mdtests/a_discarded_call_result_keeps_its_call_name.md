# A discarded call result keeps its call name

```c filename=discarded.c
int32 get(void);
_Bool flag(void);
void discard(void) {
    get();
    flag();
}
```

```click
extern int32 get() { ensures result >= 0; }
extern Bool flag() { ensures result == true; }
verifying "discarded.c";
void discard() { ensures true; } by {
    step();
    have statement(0).result >= 0 by close();
    step();
    have statement(1).result == true by close();
    have statement(0).result >= 0 by close();
    step_until(function.exit);
}
```

```expect
pass
```
