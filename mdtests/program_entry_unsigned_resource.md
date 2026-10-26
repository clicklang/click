# Startup resource regression

```c filename=main.c
unsigned int state[2] = {7, 9};
unsigned int read_pair(unsigned int *p) { return p[0] + p[1]; }
int main(void) { return read_pair(state); }
```

```click
resource pair(p: uint32*) { owns p[0..2]; }
verifying "main.c";
unsigned int read_pair(unsigned int *p) {
    owns pair(p);
    ensures to_integer(result) == to_integer(old(p[0]) + old(p[1]));
} by { unfold(pair(p)); execute(); fold(pair(p)); solve(); }
int main() {
    ensures result == 16;
} by { fold(pair(state)); }
```

```expect
pass
```

