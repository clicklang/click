# mdtest file format

This is the minimal mdtest shown in the testing and maintainer guides: a named
C block, one Click block, and an expected result.

```c filename=example.c
int32 example() {
    return 0;
}
```

```click
verifying "example.c";

int32 example() {
    ensures result == 0 by auto();
}
```

```expect
pass
```
