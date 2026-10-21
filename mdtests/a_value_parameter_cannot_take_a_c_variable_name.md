# A contract value parameter cannot take a C variable's name

The C global `k` is written by the body. A contract value parameter
`let k: int32;` would make `k` in a clause read the parameter while the body
reads the global, so this proof would show `k == 5` although the body sets
the global to 7. A value parameter is refused a C variable's name, as it is
a C parameter's.

```c filename=value_parameter_named_like_a_global.c
int k;
void f(int *p) { k = 7; }
```

```click
verifying "value_parameter_named_like_a_global.c";

resource seg(p: int32*, n: int32) {
    owns p[0..1];
    fact p[0] == n;
}

void f(int32* p) {
    let k: int32;
    owns seg(p, k);
    requires k == 5;
    ensures k == 5;
} by {
    execute();
    simp();
}
```

```expect
fail: contract value parameter `k` takes the name of a C variable
```
