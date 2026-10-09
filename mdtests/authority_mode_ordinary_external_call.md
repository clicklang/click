# An ordinary external contract applies in authority mode

`set_one` moves only memory, so its assumed contract reaches no population
and the call applies in an authority-mode project.

```c filename=ordinary_external_call.c
extern void set_one(int32* p);
void caller(int32* p) { set_one(p); }
```

```click
verifying "ordinary_external_call.c";

extern void set_one(int32* p) {
    owns p[0..1];
    ensures p[0] == 1;
}

void caller(int32* p) {
    owns p[0..1];
    ensures p[0] == 1;
} by { execute(); simp(); }
```

```expect
pass
```
