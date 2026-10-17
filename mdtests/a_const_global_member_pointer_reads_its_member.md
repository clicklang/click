# An immutable global member pointer can read its member

```c filename=static.c
struct pair { int32 first; int32 second; };
struct pair value;
int32 *const slot = &value.first;
int32 read_static(void) { return slot[0]; }
```

```click
verifying "static.c";
int32 read_static() {
    views slot;
    views value.first;
    views value.second;
} by { execute(); }
```

```expect
pass
```
