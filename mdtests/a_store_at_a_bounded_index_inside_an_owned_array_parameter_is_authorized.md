# a store at a bounded index inside an owned array parameter is authorized

The parameter companion of
`a_store_at_a_bounded_index_inside_an_owned_global_array_is_authorized.md`:
the same store, into caller memory the contract owns through `buf`, which the
resource transition authorizes at the store.

```c filename=a_store_at_a_bounded_index_inside_an_owned_array_parameter_is_authorized.c
void set_upper(int32* buf, int32 j) {
    buf[j] = 5;
}
```

```click
verifying "a_store_at_a_bounded_index_inside_an_owned_array_parameter_is_authorized.c";

void set_upper(int32* buf, int32 j) {
    owns buf[0..1000];
    requires 500 <= j and j < 1000;
    ensures buf[j] == 5 by auto;
}
```

```expect
pass
```
