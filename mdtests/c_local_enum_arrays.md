# Local enum arrays use their compatible integer type

The original two-mode array needs no source adaptation. Signed and unsigned
enums, values above `INT_MAX`, anonymous typedefs and multidimensional arrays
use the same element representation and safety checks as integer arrays.
An enum object may also hold a representable value with no named enumerator.

```c filename=mode.c
enum mode { MODE_OFF, MODE_ON };

int is_on(void) {
    enum mode modes[2];
    modes[0] = MODE_OFF;
    modes[1] = MODE_ON;
    return modes[1] == MODE_ON;
}

enum direction { DOWN = -1, UP = 1 };
int signed_modes(void) {
    enum direction modes[2];
    modes[0] = DOWN;
    modes[1] = UP;
    return modes[0] == -1 && modes[1] == 1;
}

enum flag { LOW = 0, HIGH = 2147483648U };
unsigned int high_flag(void) {
    enum flag flags[2];
    flags[0] = LOW;
    flags[1] = HIGH;
    return flags[1];
}

typedef enum { IDLE, READY } state_t;
int enum_grid(void) {
    state_t grid[2][2];
    grid[0][1] = IDLE;
    grid[1][0] = READY;
    return grid[0][1] == IDLE && grid[1][0] == READY;
}

unsigned long enum_array_size(void) {
    enum mode modes[3];
    return sizeof(modes);
}

unsigned int enum_array_compatible_values(void) {
    enum mode modes[2];
    modes[0] = 42;
    return modes[0];
}
```

```click
verifying "mode.c";

int32 is_on() {
    ensures result == 1;
}

int32 signed_modes() { ensures result == 1; }
uint32 high_flag() { ensures result == 2147483648u32; }
int32 enum_grid() { ensures result == 1; }
uint64 enum_array_size() { ensures result == 12u64; }
uint32 enum_array_compatible_values() { ensures result == 42u32; }
```

```expect
pass
```
