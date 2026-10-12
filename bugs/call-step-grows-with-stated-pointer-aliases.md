# A call step grows with stated aliases of a kept object

A call step's cost must not depend on how many equalities the path states
about memory the call does not take. A caller that owns `*b` and requires N
other parameters equal to `b` pays, at an unrelated call, work that grows with
N.

Reproduced on master `0d2b58555`:

```sh
python3 scripts/step-scaling-hunt.py aliases --sizes 1,8,32,64
```

The shape owns `*b`, requires `qi == b` for i < N, stores `b->v = 1`, calls
`touch(flags, data, k)`, and sums `qi->v`. The call step charges 3,376, 6,832
and 16,816 units at N = 8, 32 and 64. A profile at N = 256 attributes most of
the time to `related_memory_base_roots`, which rebuilds the alias-root index
over every stated equality during the call's resource composition.

Acceptance: a multi-size regression over `aliases` shows the call step's
work and time constant in N up to logarithmic factors; the summed reads still
resolve through the aliases; no budget or threshold is raised.
