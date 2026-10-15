# An owned composite unfolds a quantified definedness fact over its body

`bytes_set(p, n)` owns `p[0..n]` and states that each of those bytes is
defined. `last` consumes the composite, unfolds it, and reads `p[3]`: the
unfolded fact supplies the definedness the read needs. The folded instance
held the bytes exclusively, so the fact needs no loan; the unfold accepts it
because the body's owned range covers every byte it reads, as an ambient
owned range would. A non-quantified fact over the same range already
unfolded; the quantified one was refused as reading "memory outside every
live viewed-memory dependency".

```c filename=an_owned_composite_unfolds_its_quantified_definedness_fact.c
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

verifying "an_owned_composite_unfolds_its_quantified_definedness_fact.c";

uint8 last(uint8* p) {
    consumes bytes_set(p, 4u64);
    produces p[0u64..4u64];
} by {
    unfold(bytes_set(p, 4u64));
    execute();
}
```

```expect
pass
```
