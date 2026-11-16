# Static scalar references retain their value type

The address used by a typed memory read is a byte address; naming the scalar
value does not require a C pointer-to-that-type carrier.

```c filename=c_static_scalar_declaration_types.c
int32 bool_holder(void) {
    static const _Bool ready = 1;
    return 0;
}

int32 pointer_holder(void) {
    static int32** chain;
    return 0;
}
```

```click
verifying "c_static_scalar_declaration_types.c";

int32 bool_holder() {
    ensures bool_holder.static(0) == true;
}

int32 pointer_holder() {
    owns pointer_holder.static(0).storage()[0..8];
    ensures pointer_holder.static(0) == pointer_holder.static(0);
}
```

```expect
pass
```
