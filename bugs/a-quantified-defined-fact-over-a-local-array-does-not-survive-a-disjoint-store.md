# A quantified `defined` fact over a local array does not survive a disjoint store

Soundness: sound. A fact is dropped, so a valid proof is refused; nothing
false verifies.

The violated invariant: a fact about memory that a step does not change is
still available after the step. A store to one local leaves every byte of
another local unchanged, and a value fact over that other local does survive
the store. The `defined` fact over the same bytes, stated the same way, does
not. `mdtests/guarded_definedness_survives_a_disjoint_store.md` checks that a
range-bounded `defined` fact survives a disjoint store.

## Reproduction

`a-quantified-defined-fact-over-a-local-array-does-not-survive-a-disjoint-store.click`
and its `.c`:

```c
char tmp[4];
int unit;
tmp[0] = 'a';
tmp[1] = 0;
unit = j;
```

The proof states both facts after the two stores to `tmp`:

```click
have forall (k: uint64) { 0u64 <= k and k < 1u64 implies tmp[k] != 0u8 } by { enumerate(); }
have forall (k: uint64) { 0u64 <= k and k < 2u64 implies defined(tmp[k]) } by { enumerate(); }
step();
have forall (k: uint64) { 0u64 <= k and k < 1u64 implies tmp[k] != 0u8 } by { assumption(); }
have forall (k: uint64) { 0u64 <= k and k < 2u64 implies defined(tmp[k]) } by { assumption(); }
```

After the `step()` over `unit = j;`, the value fact is still available, but
the `defined` one is refused:

```text
`assumption` requires the current goal as an available semantic fact
current goal is a universal proposition
goal: forall (k: uint64) { true and k < 2u64 implies defined(*<pointer A>) }
```

An explicit `transport` from a mark before the store carries it, so the frame
can justify it:

```click
mark before;
step();
transport(forall (k: uint64) { 0u64 <= k and k < 2u64 implies defined(at(before, tmp[k])) },
          forall (k: uint64) { 0u64 <= k and k < 2u64 implies defined(tmp[k]) });
```

Found while proving Linux `string_get_size`
(`examples/string-get-size/`). That proof transports the fraction buffer's
`defined` fact this way after the store to `unit` in each of its 19 unit
cases.

## Acceptance criteria

- The reproduction's last `have` closes with `assumption()`: a quantified
  `defined` fact over memory a step does not write survives the step, as the
  value fact over the same bytes does.
- A regression keeps this pattern: a quantified `defined` fact over a local
  array, a store to a different local, and the fact used afterwards.
- `examples/string-get-size/` can drop its per-case `transport` of the
  fraction's `defined` fact.
