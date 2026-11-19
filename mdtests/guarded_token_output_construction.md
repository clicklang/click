# A guarded output token is constructed when owed

The contract authorizes both returns to construct a token, but only the
positive branch owes one.

```c filename=token.c
int32 when_positive(int32 n) {
    if (n > 0) { return 3; }
    return 4;
}
```

```click
abstract resource ticket(n: int32);

verifying "token.c";

int32 when_positive(int32 n) {
    constructs ticket(result);
    if n > 0 { produces ticket(result); }
}
```

```expect
pass
```
