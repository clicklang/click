# A C parameter named `result` keeps its binding through casts

```c filename=bump.c
int32 bump(int32 result) {
    return result + 1;
}
```

```click
verifying "bump.c";

int32 bump(int32 result) {
    requires 0 <= program::result and program::result <= 100;
    ensures to_integer(result) == to_integer((program::result as int32) + 1);
    ensures to_integer(((program::result + result) as int32)) == to_integer(program::result + result);
}
```

```expect
pass
```
