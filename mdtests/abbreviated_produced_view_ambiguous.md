# Two direct input matches require a named source

```c filename=ambiguous_view.c
int *first(int *p) { return p; }
```

```click
verifying "ambiguous_view.c";

int32* first(int32* p) {
    views *p as first_input;
    views p[0..1] as second_input;
    produces view(*p);
    ensures result == p;
}
```

```expect
fail: matches multiple input views; name its input with `views ... as name` and write `from name`
```
