# An enum with no negative value is unsigned

GCC and Clang give an enumeration with no negative value the compatible type
`unsigned int`, and one with a negative value `int`. Click modeled every enum
object as `int32`, so for `tag == IDLE` it proved that `j->tag - 1 < 0` holds,
while both compilers compute `0u - 1` as `UINT_MAX` and return `0`. An enum
object now takes its compatible type, so Click proves the compilers' result;
see
`an_enum_with_a_negative_value_is_signed.md` for the signed case.

```c filename=unsigned_enum_field.c
enum state { IDLE, BUSY };

struct job {
	enum state tag;
};

int below_idle(struct job *j)
{
	return j->tag - 1 < 0;
}
```

```click
verifying "unsigned_enum_field.c";

int32 below_idle(struct job *j) {
    requires j->tag == 0;
    views j->tag;
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
pass
```
