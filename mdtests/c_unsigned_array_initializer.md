# Unsigned integer array initializers preserve values and zero-fill omissions

The original C initializer is unchanged. The same typed initializer path
handles omitted elements, nested dimensions, constant conversions, symbolic
values and enums whose compatible type is unsigned int.

```c filename=array.c
unsigned int second(void) {
    unsigned int values[2] = { 10u, 20u };
    return values[1];
}
unsigned int zero_tail(void) {
    unsigned int values[4] = { 7u };
    return values[3];
}

unsigned int matrix(void) {
    unsigned int values[2][3] = { { 1u, 2u }, { 3u } };
    return values[0][1] + values[1][0] + values[1][2];
}

int converts_constants(void) {
    unsigned int values[2] = { -1, 4294967297ULL };
    return values[0] == 4294967295u && values[1] == 1u;
}

unsigned int symbolic(unsigned int value) {
    unsigned int values[2] = { value };
    return values[0] + values[1];
}

enum mode { MODE_OFF, MODE_ON };
int enum_initializer(void) {
    enum mode values[2] = { MODE_OFF, MODE_ON };
    return values[1] == MODE_ON;
}
```

```click
verifying "array.c";
uint32 second() { ensures result == 20u32; }
uint32 zero_tail() { ensures result == 0u32; }
uint32 matrix() { ensures result == 5u32; }
int32 converts_constants() { ensures result == 1; }
uint32 symbolic(uint32 value) { ensures result == value; }
int32 enum_initializer() { ensures result == 1; }
```

```expect
pass
```
