# A designated inferred array has the largest index plus one elements

`static const unsigned int table[] = { [3] = 7 };` has four elements, so
`table[4]` is out of bounds and refused; see
`string_get_size_tables_take_designators_sizeof_and_literal_branches.md` for
the elements it holds.

```c filename=designated_bound.c
unsigned int padded(int index)
{
	static const unsigned int table[] = { [3] = 7 };

	return table[index];
}
```

```click
verifying "designated_bound.c";

uint32 padded(int32 index) {
    requires index == 4;
    ensures true;
} by {
    execute();
    simp();
}
```

```expect
fail: array subobject index must be at least 0 and less than 4
```
