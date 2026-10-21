# An enum with a negative value is signed

An enumeration with a negative value has the compatible type `int`, so
`d - 2 < 0` is true for `d == UP`; see
`an_enum_with_no_negative_value_is_unsigned.md` for the unsigned case. The
parameter and its sidecar spelling take that type, `int32`.

```c filename=signed_enum_parameter.c
enum direction { DOWN = -1, UP = 1 };

int below_two(enum direction d)
{
	return d - 2 < 0;
}
```

```click
verifying "signed_enum_parameter.c";

int32 below_two(int32 d) {
    requires d == 1;
    ensures result == 1;
} by {
    execute();
    simp();
}
```

```expect
pass
```
