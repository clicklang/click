# A store at a symbolic index grows with the path's order facts

A store `data[xi] = i` must cost work proportional to the store. With the
indices ordered by a chain of facts `x0 < x1 < ... < xN`, each later store
costs more than the one before, so N stores are quadratic.

Reproduced on master `0d2b58555`:

```sh
python3 scripts/step-scaling-hunt.py order_chain --sizes 1,8,32,64
```

The shape owns `data[0..len]`, requires the chain, stores `data[x0] = 100`
and then `data[xi] = i` for i = 1..N, and reads `data[x0]`. The largest store
step charges 419, 1,211 and 2,267 units at N = 8, 32 and 64, and grows with
the store's position. A profile at N = 192 attributes most of the time to
`pointer_offset_by_elements_paths` deciding the address arithmetic against
every order fact (`decide_with_facts`), and part to the store forgetting
cached cells it may write, which asks distinctness of every cached cell of
the array.

Acceptance: a multi-size regression over `order_chain` shows each store
step's work and time constant in N up to logarithmic factors; the final read
still resolves `data[x0]` to 100; no budget or threshold is raised.
