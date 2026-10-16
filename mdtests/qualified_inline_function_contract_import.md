# An imported qualified contract retains the declaring file's alias binding

```c filename=qualified_inline_function_first.c
static inline int helper(void) { return 1; }
int first_use(void) { return helper(); }
```

```c filename=second.c
static inline int helper(void) { return 2; }
int second_use(void) { return helper(); }
```

```click
import "qualified_inline_function_import.click";
verifying "qualified_inline_function_first.c";
verifying "second.c" as selected;
int32 first_use() { ensures result == 1; } by {
    let { result: answer } = step(selected::helper(), {});
    execute(); simp();
}
int32 second_use() { ensures result == 2; } by { execute(); simp(); }
```

```expect
pass
```
