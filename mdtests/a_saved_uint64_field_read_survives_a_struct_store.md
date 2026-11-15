# A saved uint64 field read survives a struct store

The saved read keeps the pre-store value while the other field remains
unchanged. A no-write declaration may share byte-read identity with a cached
observation that names the read itself; registering that observation must
finish rather than repeatedly queueing its own stored value.

```c filename=wide_observation.c
struct State { unsigned long state; unsigned long inc; };
unsigned long read(struct State* rng) {
    unsigned long oldstate = rng->state;
    rng->state = oldstate + rng->inc;
    return oldstate;
}
```

```click
import click::integer;
verifying "wide_observation.c";
uint64 read(struct State* rng) {
    owns *rng;
    ensures result == old(rng->state);
    ensures rng->state == old(integer::uint64_wrapping_add(rng->state, rng->inc));
    ensures rng->inc == old(rng->inc);
}
```

```expect
pass
```
