# The shape of a Click file

A `.click` file names its C source with `verifying` and attaches a contract
block, with requirements and a labeled guarantee, to each C function.

```c filename=file.c
int32 function_name(int32 p[], int32 n) {
    return n;
}
```

```click
verifying "file.c";

int32 function_name(int32 p[], int32 n) {
    requires n >= 0;
    requires viewable(p[0..n]);
    ensures label: result == n by auto();
}
```

```expect
pass
```
