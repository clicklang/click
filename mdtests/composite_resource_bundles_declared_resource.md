# A composite resource bundles a declared resource with memory

The body of `uncalled` owns another declared resource, `socket_open(7)`,
beside a memory range and a pure fact, and `fold` packages all three.

```c filename=init_socket_flag.c
int32 init_socket_flag(int32 flag[]) {
    flag[0] = 0;
    return 0;
}
```

```click
abstract resource socket_open(fd: int32);

resource uncalled(flag: int32*) {
    owns socket_open(7);
    owns flag[0..1];
    fact flag[0] == 0;
}

verifying "init_socket_flag.c";

int32 init_socket_flag(int32 flag[]) {
    consumes socket_open(7);
    consumes flag[0..1];

    produces uncalled(flag) by {
        execute();
        fold(uncalled(flag));
    }
}
```

```expect
pass
```
