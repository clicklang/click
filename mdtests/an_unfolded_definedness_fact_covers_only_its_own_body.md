# An unfolded definedness fact covers only its own body

The negative twin of
[`an_owned_composite_unfolds_its_quantified_definedness_fact.md`](an_owned_composite_unfolds_its_quantified_definedness_fact.md).
`bytes_set(p, 3)` owns and defines only `p[0..3]`, so after the unfold the
read of `p[3]` has no authority: the unfolded owned range supports the body
fact, not memory past it.

```c filename=an_unfolded_definedness_fact_covers_only_its_own_body.c
uint8 last(uint8 *p)
{
	return p[3];
}
```

```click
resource bytes_set(p: uint8*, n: uint64) {
    owns p[0..n];
    fact n < 1024u64;
    fact forall (k: uint64) { 0u64 <= k and k < n implies defined(p[k]) };
}

verifying "an_unfolded_definedness_fact_covers_only_its_own_body.c";

uint8 last(uint8* p) {
    consumes bytes_set(p, 3u64);
    produces p[0u64..3u64];
} by {
    unfold(bytes_set(p, 3u64));
    execute();
}
```

```expect
fail: missing resource fact `views p[3]`
```
