# A fact about `result` is not cited at function entry

`result` exists only once the function returns, so a fact that names it
cannot be read at `function.entry`. When `auto` cites the `have` about
`result` below, its expansion spells the fact as written instead of
anchoring it at entry, which would not parse.

```c filename=a_fact_about_result_is_not_cited_at_function_entry.c
unsigned decrement(unsigned x) { return x - 1u; }
```

```click
import click::integer;
verifying "a_fact_about_result_is_not_cited_at_function_entry.c";

uint32 decrement(uint32 x) {
    requires 1u32 <= x;
    ensures to_integer(result) <= to_integer(x) by {
        execute();
        have to_integer(result) == to_integer(x) - 1 by {
            apply(uint32_subtract_to_integer(x, 1u32)) using { 1u32 <= x; }
        }
        have to_integer(result) <= to_integer(x) by auto();
    }
}
```

```expect
pass
```
