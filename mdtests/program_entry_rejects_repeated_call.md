# Calling main is not another program startup

```c filename=main.c
int state = 7;
int main(void) { state += 1; return state; }
int again(void) { main(); return main(); }
```

```click
verifying "main.c";
int main() { ensures result == 8; } by { execute(); solve(); }
int again() {
    owns state;
    ensures result == 8;
} by { execute(); solve(); }
```

```expect
fail: again.contract
```
