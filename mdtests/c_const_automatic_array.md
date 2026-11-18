# A const automatic array can use a runtime initializer

```c filename=port.c
int select_port(int use_default, int configured_port) {
    const int ports[] = { configured_port, 8080 };
    return use_default ? ports[1] : ports[0];
}
```

```click
verifying "port.c";
int32 select_port(int32 use_default, int32 configured_port) {
    ensures use_default == 0 implies result == configured_port;
    ensures use_default != 0 implies result == 8080;
}
```

```expect
pass
```
