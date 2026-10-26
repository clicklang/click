# Scalar globals require one linked definition

```c filename=left.c
int32 counter = 1;

int32 left() {
    return counter;
}
```

```c filename=right.c
int32 counter = 2;

int32 right() {
    return counter;
}
```

```click
verifying "left.c";
verifying "right.c";

int32 left() {
    ensures result == 1;
}

int32 right() {
    ensures result == 2;
}
```

```expect
fail: multiple definitions of global `counter`
```
