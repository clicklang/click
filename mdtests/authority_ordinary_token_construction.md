# An ordinary token is constructed

`pair` is an abstract resource declared without `authorized`, so its tokens
are not population members. At return, the proof constructs the token owed
by `produces` using the matching `constructs` clause. If the token is needed
inside a composite, the proof can construct it explicitly before folding.

```c filename=bump.c
int32 bump(int32 result) {
    return result + 1;
}

int32 pack(int32 n) {
    return n;
}
```

```click
abstract resource pair(returned: int32, input: int32);
resource wrapped(n: int32) {
    owns pair(n, n);
}

verifying "bump.c";

int32 bump(int32 result) {
    requires 0 <= program::result and program::result <= 100;
    constructs pair(result, program::result);
    produces pair(result, program::result) by {
        step_until(function.exit);
    }
}

int32 pack(int32 n) {
    constructs pair(result, result);
    produces wrapped(result);
} by {
    step_until(function.exit);
    fold(pair(result, result));
    fold(wrapped(result));
}
```

```expect
pass
```
