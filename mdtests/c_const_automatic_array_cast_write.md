# A const automatic array stays read-only through a cast

```c filename=port.c
int change_port(int configured_port) {
    const int ports[3] = { configured_port };
    int *alias = (int *)ports;
    alias[2] = 8080;
    return ports[2];
}
```

```click
verifying "port.c";
int32 change_port(int32 configured_port) {
    ensures result == result;
}
```

```expect
fail: invalid memory access
```
