# Multiple statements preserve an abstract resource field

```c filename=keep.c
void keep(unsigned char *p) { *p = 0; *p = 1; }
```

```click
verifying "keep.c";
abstract resource model() { field value: int32; }
void keep(uint8* p) {
    owns *p;
    owns m: model();
    requires separate(memory(*p), m);
} by {
    step();
    have separate(statement(0).footprint, m) by {
        normalize() using { separate(memory(*p), m); };
    }
    step();
    have separate(statement(1).footprint, m) by {
        normalize() using { separate(memory(*p), m); };
    }
    have m.value == at(statement(0).entry, m.value) by {
        have m.value == at(statement(0).entry, m.value) by {
            normalize() using {
                at(statement(0).entry, m.value) == at(statement(0).entry, m.value);
            };
        }
        assumption();
    }
    step();
}
```

```expect
pass
```
