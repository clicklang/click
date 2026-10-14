# `&object.field` names that field's storage, not the object's first cell

An `owns object.field` clause on a static-storage aggregate has to carry the
field's ABI offset. Taking the address is part of the segment's base form, not
part of the place, so the field resolves the same way it does without the `&`.
Writing one field while owning the other is out of bounds.

`keep_second` reads the untouched field in its entry state: `old(shared.second)`
names the same static place as `shared.second`, so the implicit closer proves
the field unchanged.

```c filename=static_struct_field_footprint.c
struct pair {
    int32 first;
    int32 second;
};

struct pair shared;

int32 write_first() {
    shared.first = 9;
    return 0;
}

int32 write_second() {
    shared.second = 9;
    return 0;
}

int32 keep_second() {
    shared.first = 9;
    return 0;
}
```

```click
verifying "static_struct_field_footprint.c";

int32 write_first() {
    owns shared.first;
    ensures result == 0 by auto;
}

int32 write_second() {
    owns shared.second;
    ensures result == 0 by auto;
}

int32 keep_second() {
    owns shared;
    ensures result == 0;
    ensures shared.second == old(shared.second);
}
```

```expect
pass
```
