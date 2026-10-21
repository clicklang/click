# A pointer-table load at an undecided index reports false undefined behavior

Soundness: incomplete. No false claim is known to verify: with the index
decided (`requires (u & 1) == 1`) the load reads the right object, and a wrong
`ensures` is refused. With the index undecided, Click refuses a valid program
and names an undefined behavior that does not happen.

The violated invariant: a load from an in-bounds element of a static array of
object pointers yields one of the stored pointers, so indexing through it is
defined whenever it is defined for each stored pointer. `execute()` should
either split the stored pointers into paths or keep the value symbolic.
Instead it reports `pointer arithmetic left the pointed-to object` with the goal
`(u & 1u32) * 8 == 8`. That goal says the element offset must be 8, which
is only the case where the second element is selected.

The reproduction uses only forms Click supported before string tables:
`&a[0]` initializers in a function-scope `static` pointer array.

```c filename=k1.c
static int a[2] = { 3, 4 };
static int b[2] = { 5, 6 };
int f(unsigned int u)
{
	static int *const t[] = { &a[0], &b[0] };
	return t[u & 1][1];
}
```

```click
verifying "k1.c";
int32 f(uint32 u) {
    ensures true;
} by {
    execute();
    simp();
}
```

Click reports:

```text
`execute()` produced undefined behavior
pointer arithmetic left the pointed-to object
C statement at k1.c:6:2
`return t[u & 1][1];`
goal: (u & 1u32) * 8 == 8
```

The scalar form, `static int *const t[] = { &a, &b }; return *t[u & 1];`,
fails differently. Its message names a resource that treats the loaded
pointer as an offset into `t` itself:
`missing resource fact views (char *)&t#static0 + *((char *)&t#static0 + (u & 1) * 8) * 4`.

Linux's `string_get_size` reaches this with
`unit = units_str[units_base][i];`, where `units_base` is `units & 1`. A
proof can avoid it by splitting on `units_base` before the load.

Acceptance criteria:

- `k1.c` above verifies with `execute(); simp();`, and `ensures result == 4 or
  result == 6` verifies when `a` and `b` are `const`.
- The scalar `*t[u & 1]` form verifies the same way.
- With the index decided, the existing behavior is unchanged, and a wrong
  `ensures` is still refused.
