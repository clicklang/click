# Nested getter arguments still require memory authority

```c filename=nested-arguments.c
int marker(void) { return 0; }
```

```click
verifying "nested-arguments.c";
function identity(value: int32) -> int32 { value }
resource bad(root: int32*, other: int32*) {
    owns *other;
    fact identity(identity(*root)) == 0;
}
int32 marker() { ensures result == 0; } by { execute(); simp(); }
```

```expect
fail: current read authority
```
