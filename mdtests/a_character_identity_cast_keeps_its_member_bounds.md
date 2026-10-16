# An identity character-pointer cast retains the existing byte view

```c filename=bytes.c
struct bytes { signed char first; signed char second; };
signed char read_byte(struct bytes* p) {
    signed char* q = (signed char*)&p->first;
    return q[1];
}
```

```click
verifying "bytes.c";
int8 read_byte(struct bytes* p) {
    requires p != 0;
    views p->first;
    views p->second;
} by { execute(); simp(); }
```

```expect
fail: outside
```
