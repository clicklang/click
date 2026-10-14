# Consuming and producing one declared resource is spelled `owns`

A declared resource at the same parameters, consumed and produced, is the
borrow `owns cell(p);`. The produced clause's proof moves with it.

```c filename=consumes_and_produces_one_resource_is_owns.c
void set(int32 p[], int32 x) {
    p[0] = x;
}
```

```click
verifying "consumes_and_produces_one_resource_is_owns.c";

resource cell(p: int32*) {
    owns p[0..1];
}

void set(int32 p[], int32 x) {
    consumes cell(p);
    produces cell(p) by auto;
}
```

```expect
fail: `set` consumes and produces `cell(p)`; write the one clause `owns cell(p);`, with the `produces` clause's proof
```
