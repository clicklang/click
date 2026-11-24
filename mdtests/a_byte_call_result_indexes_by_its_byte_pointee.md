# A byte call result indexes by its byte pointee

`statement(0).call(make, 0).result` names `make`'s `uint8 *` result, so
`result[1]` is the byte at offset 1. Click once took no element type from a
call result and read `result[1]` as an `int32` cell, so `known()` did not
find this fact.

```c filename=byte_call_result.c
struct holder { uint8* p; };
uint8* make(void);
void f(struct holder* h) {
    h->p = make();
    free(h->p);
}
```

```click
extern uint8* make() {
    produces allocation(result, 2);
    produces result[0..2];
    ensures result[1] == 9u8;
}
verifying "byte_call_result.c";
void f(struct holder* h) {
    owns h->p;
} by {
    step();
    have statement(0).call(make, 0).result[1] == 9u8 by {
        known();
    }
    step_until(function.exit);
}
```

```expect
pass
```
