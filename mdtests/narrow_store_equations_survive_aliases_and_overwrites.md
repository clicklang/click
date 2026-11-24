# Narrow store equations survive aliases and overwrites

Signed and unsigned byte and halfword stores retain their equations at the
written program point, including values with their high bit set.

```c filename=put.c
void put_i8(int8* p, int8* q) { *p = -15; *p = 4; }
void put_u8(uint8* p, uint8* q) { *p = 241; *p = 4; }
void put_i16(int16* p, int16* q) { *p = -255; *p = 4; }
void put_u16(uint16* p, uint16* q) { *p = 65281; *p = 4; }
```

```click
verifying "put.c";
void put_i8(int8* p, int8* q) {
    requires p == q;
    owns p[0..1];
    ensures *p == 4;
} by {
    step();
    mark first;
    have *p == -15 by { close(); }
    have *q == -15 by { rewrite(q, p); close(); }
    step();
    have *p == 4 by { close(); }
    have at(first, *p) == -15 by { close(); }
}
void put_u8(uint8* p, uint8* q) {
    requires p == q;
    owns p[0..1];
    ensures *p == 4;
} by {
    step();
    mark first;
    have *p == 241 by { close(); }
    have *q == 241 by { rewrite(q, p); close(); }
    step();
    have *p == 4 by { close(); }
    have at(first, *p) == 241 by { close(); }
}
void put_i16(int16* p, int16* q) {
    requires p == q;
    owns p[0..1];
    ensures *p == 4;
} by {
    step();
    mark first;
    have *p == -255 by { close(); }
    have *q == -255 by { rewrite(q, p); close(); }
    step();
    have *p == 4 by { close(); }
    have at(first, *p) == -255 by { close(); }
}
void put_u16(uint16* p, uint16* q) {
    requires p == q;
    owns p[0..1];
    ensures *p == 4;
} by {
    step();
    mark first;
    have *p == 65281 by { close(); }
    have *q == 65281 by { rewrite(q, p); close(); }
    step();
    have *p == 4 by { close(); }
    have at(first, *p) == 65281 by { close(); }
}
```

```expect
pass
```
