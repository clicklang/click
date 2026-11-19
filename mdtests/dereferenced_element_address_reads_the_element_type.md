# `*&p[i]` reads `p`'s element type

`&p[i]` points at `p`'s element, so `*&p[i]` reads exactly what `p[i]` reads:
one `char` through a `char *`, one byte through an `unsigned char *`. It is
not a four-byte `int32` read at that address, which would also read the
next three bytes.

```c filename=element_address.c
void set_c(char *p) { p[0] = 1; p[1] = -3; p[2] = 5; p[3] = 7; }
void set_u(unsigned char *p) { p[0] = 1; p[1] = 2; p[2] = 3; p[3] = 4; }
```

```click
verifying "element_address.c";
void set_c(char* p) {
    owns p[0..4];
    ensures *&p[1] == -3 by {
        step();
        step();
        step();
        step();
        step();
        known();
    }
}
void set_u(uint8* p) {
    owns p[0..4];
    ensures *&p[0] == 1u8 by {
        step();
        step();
        step();
        step();
        step();
        known();
    }
}
```

```expect
pass
```
