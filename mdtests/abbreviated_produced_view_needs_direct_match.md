# A proved pointer equality does not select an omitted source

```c filename=alias_view.c
int *first(int *p) { return p; }
```

```click
verifying "alias_view.c";

int32* first(int32* p) {
    views *p as input;
    produces view(*result);
    ensures result == p;
}
```

```expect
fail: has no direct match; name its input with `views ... as name` and write `from name`
```
