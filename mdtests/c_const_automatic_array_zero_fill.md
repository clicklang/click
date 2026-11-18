# A const automatic array zero-fills omitted elements

```c filename=port.c
int last_port(int configured_port) {
    const int ports[1000000] = { configured_port };
    return ports[999999];
}
```

```click
verifying "port.c";
int32 last_port(int32 configured_port) {
    ensures result == 0;
}
```

```expect
pass
```
