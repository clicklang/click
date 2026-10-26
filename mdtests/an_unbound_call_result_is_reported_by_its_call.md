# An unbound call result is reported by its call

`make()`'s allocation is stored in `h->p` and then overwritten, so no local
or cell names it, yet the caller still owns it. The report spells it by the
call that introduced it, `statement(0).call(make, 0).result`, rather than a
report-local `<pointer A>`.

```c filename=unbound_call_result.c
struct holder { int32* p; };
int32* make(void);
void f(struct holder* h) {
    h->p = make();
    h->p = 0;
}
```

```click
extern int32* make() {
    produces allocation(result, 8);
    produces result[0..2];
    ensures result[0] == 7;
}
verifying "unbound_call_result.c";
void f(struct holder* h) {
    owns h->p;
    ensures false;
}
```

```expect
fail: owns allocation(statement(0).call(make, 0).result, 8)
```
