# Four character writes initialize the declared unsigned integer

The integer starts uninitialized. The helper writes its little-endian bytes
through an ordinary character pointer, in a different call frame. The typed
observation must agree with the four bytes written by the helper.

```c filename=initialize_word.c
void fill(unsigned char *bytes) {
    bytes[3] = 255;
    bytes[1] = 128;
    bytes[0] = 17;
    bytes[2] = 238;
}
unsigned int decode(void) {
    unsigned int obj;
    unsigned char *bytes = (unsigned char *)(void *)&obj;
    fill(bytes);
    return obj;
}
```

```click
verifying "initialize_word.c";
import click::integer;

void fill(uint8* bytes) {
    consumes uninitialized(bytes[0..4]);
    produces bytes[0..4];
    ensures bytes[0] == 17;
    ensures bytes[1] == 128;
    ensures bytes[2] == 238;
    ensures bytes[3] == 255;
}

uint32 decode() {
    ensures result == 4293820433u32;
} by {
    step_until(statement(3));
    have bytes[0] == 17;
    have bytes[1] == 128;
    have bytes[2] == 238;
    have bytes[3] == 255;
    have defined(obj);
    have viewable((&obj)[0..1]);
    apply(integer::uint32_from_le_bytes(&obj)) using {
        little_endian();
        viewable((&obj)[0..1]);
        defined(obj);
    };
    have obj == 4293820433u32;
}
```

```expect
pass
```
