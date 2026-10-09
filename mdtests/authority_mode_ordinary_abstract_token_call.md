# An ordinary abstract token moves through calls in authority mode

`permit` is an abstract resource declared without `authorized`, so it takes
no part in population accounting. The callback contract that preserves
permits applies in an authority-mode project as it does without authority
semantics.

```c filename=framed_callback_token.c
int32 keep_first(int32 key, int32 spare) {
    return key;
}

int32 apply_keep(
    int32 (*callback)(int32, int32),
    int32 key,
    int32 spare
) {
    return callback(key, spare);
}

int32 framed_token_caller(int32 key, int32 spare) {
    return apply_keep(&keep_first, key, spare);
}
```

```click
abstract resource permit(key: int32);

verifying "framed_callback_token.c";

contract int32 PreservePair(int32 key, int32 spare) {
    owns permit(key);
    owns permit(spare);
    ensures result == key;
}

int32 keep_first(int32 key, int32 spare) {
    owns permit(key);
    ensures result == key;
} by {
    execute();
    simp();
}

int32 apply_keep(
    int32 (*callback)(int32, int32),
    int32 key,
    int32 spare
) {
    requires PreservePair(callback);
    owns permit(key);
    owns permit(spare);
    ensures result == key;
} by {
    execute();
    simp();
}

int32 framed_token_caller(int32 key, int32 spare) {
    owns permit(key);
    owns permit(spare);
    ensures result == key;
} by {
    execute();
    simp();
}
```

```expect
pass
```
