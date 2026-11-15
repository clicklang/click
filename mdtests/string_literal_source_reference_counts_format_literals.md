# Specially lowered format literals retain their source occurrence

```c filename=literal_format.c
int snprintf(char *buf, unsigned long size, const char *fmt, ...);
const char* formatted(char* out) {
    snprintf(out, 1, "format");
    return "after";
}
```

```click
target "x86_64-unknown-linux-gnu";
mode "kernel";
verifying "literal_format.c";
const char* formatted(char out[]) {
    owns out[0..1];
    ensures result == formatted.string_literal(1);
}
```

```expect
pass
```
