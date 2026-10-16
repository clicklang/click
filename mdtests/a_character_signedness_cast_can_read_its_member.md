# Character signedness conversion retains the existing byte view

```c filename=bytes.c
struct bytes { signed char first; signed char second; };
unsigned char read_byte(struct bytes* p) {
    unsigned char* q = (unsigned char*)&p->first;
    return q[0];
}
```

```click
verifying "bytes.c";
uint8 read_byte(struct bytes* p) {
    requires p != 0;
    views p->first;
    views p->second;
} by { execute(); simp(); }
```

```expect
pass
```
