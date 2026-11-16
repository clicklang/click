# Static declarations have typed source references

A function's static object can be named where its pointer escapes, independently
of which function is currently executing. File-static objects have a translation
unit owner. The selectors retain C types and do not supply read permission.

```c filename=c_static_declaration_references.c
static int32 file_value = 3;
static int32 file_value;

int32* give(void) {
    static int32 value = 7;
    return &value;
}

int32 read(void) {
    int32* pointer = give();
    return *pointer;
}

int32 file_read(void) {
    return file_value;
}

struct cell { int32 value; };

int32* slot_address(void) {
    static struct cell values[2] = {{1}, {2}};
    return &values[1].value;
}

int32 read_cell(void) {
    int32* pointer = slot_address();
    return *pointer;
}
```

```click
verifying "c_static_declaration_references.c";

int32* give() {
    ensures result == &give.static(0);
}

int32 read() {
    owns give.static(0);
    ensures result == old(give.static(0));
}

int32 file_read() {
    owns "c_static_declaration_references.c"::static(0);
    ensures result == old("c_static_declaration_references.c"::static(0));
}

int32* slot_address() {
    ensures result == &slot_address.static(0)[1].value;
}

int32 read_cell() {
    owns slot_address.static(0)[1].value;
    ensures result == old(slot_address.static(0)[1].value);
}
```

```expect
pass
```
