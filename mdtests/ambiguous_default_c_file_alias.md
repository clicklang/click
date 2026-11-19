# A duplicate C filename stem needs an explicit alias when used

```c filename=left/table.c
static unsigned long count = 7;
```

```c filename=right/table.c
static unsigned long count = 19;
```

```c filename=main.c
int main(void) { return 0; }
```

```click
verifying "left/table.c";
verifying "right/table.c";
verifying "main.c";

int32 main() {
    ensures table::count == 7u64;
}
```

```expect
fail: ambiguous default C source alias `table` matches `left/table.c` and `right/table.c`. Use `as`
```
