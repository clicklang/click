# A struct-field read inside an `&&` branch fails `execute()`

## Violated invariant

`execute()` should handle a struct-array field read wherever a scalar read
works. This fails:

```c
struct point { int32 x; int32 y; };
int32 f(int32 x) {
    struct point items[2] = {{1, 2}, {3, 4}};
    int32 r = 0;
    if (0 <= x && x < 2) { r = items[x].y; }
    return r;
}
```

with "could not split … into its 5 path cases, no condition … has a Click
spelling". The same read under `requires 0 <= x; requires x < 2;` verifies
(`a_bounded_symbolic_field_read_of_an_initialized_struct_array_is_initialized.md`).
Two gaps were observed: the kernel doesn't use stride residues to tell
`x*8 + 4` apart from cells at offsets 0 and 8, and
`add_pointer_offset_equality_execution_pure_facts` doesn't turn `x*8 + 4 == 12`
into `x == 1` the way it does for `int32` elements.

## Intended regression

An mdtest with the program above and `ensures result == 0 || result == 2 ||
result == 4` (or at least `execute(); simp();` reaching the end), plus a
nested-struct variant. Negative: an index bound one past the end is refused.

## Acceptance criteria

- Field reads at a symbolic element index split into cases with Click
  spellings (`x == 0`, `x == 1`) exactly as scalar element reads do.
- Offsets that differ modulo the stride are known distinct without a case
  split.
