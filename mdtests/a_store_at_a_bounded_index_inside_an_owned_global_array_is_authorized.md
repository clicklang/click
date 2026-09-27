# a store at a bounded index inside an owned global array is authorized

`buf[j]` with `500 <= j < 1000` is element `j` of `buf[0..1000]`, which the
contract owns. The owned-footprint check for file-scope storage used to
compare byte addresses only across a constant distance, so any symbolic index
was refused as a write outside the footprint. It now reads the store in the
owned range's element coordinates and asks the fact check for `0 <= j` and
`j < 1000`.
`a_store_at_a_bounded_index_inside_an_owned_array_parameter_is_authorized.md`
is the same store through a parameter; the refusals beside the edges are
`a_store_one_past_an_owned_global_array_is_refused.md` and
`a_store_below_an_owned_global_range_is_refused.md`.

```c filename=a_store_at_a_bounded_index_inside_an_owned_global_array_is_authorized.c
int32 buf[1000];

void set_upper(int32 j) {
    buf[j] = 5;
}
```

```click
verifying "a_store_at_a_bounded_index_inside_an_owned_global_array_is_authorized.c";

void set_upper(int32 j) {
    owns buf[0..1000];
    requires 500 <= j and j < 1000;
    ensures buf[j] == 5 by auto;
}
```

```expect
pass
```
