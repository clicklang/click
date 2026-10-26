# Startup resource regression

```c filename=main.c
int state = 7;
int read_cell(int *p) { return *p; }
int main(void) { return read_cell(&state); }
```

```click
resource cell(p: int32*) { owns p[0..1]; }
verifying "main.c";
int read_cell(int *p) {
    owns cell(p);
    ensures result == old(p[0]);
} by { unfold(cell(p)); step_until(function.exit); fold(cell(p)); solve(); }
int main() { ensures result == 7; }
by { fold(cell(&state)); }
```

```expect
pass
```

