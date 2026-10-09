# One-shot release/acquire publication

`publication.c` is the frozen C11 example for the one-shot publication
milestone of the [concurrency demo](../../issues/concurrency-demo.md). The
producer initializes an ordinary payload and release-stores a ready flag; the
consumer acquire-loads the flag until it is set and then reads the payload,
before the parent joins the producer. The intended proof shows that the
consumer reads the producer's value without requiring its polling loop to
terminate.

`publication.click` proves it under the modeled-pthread runtime. The
`ready_payload(channel)` resource owns the payload and states its value.
`publish_once` hands it to `atomic_init` as the published type. `producer`
folds it and spends it with its publisher right at the release store. `consume`
keeps the subscriber right as the invariant of its diverging spin loop, and
receives `ready_payload(channel)` on the branch that sees the flag set.
`publish_once` then returns 42 after the join, or -1 when creation fails. Do
not edit the C to fit the verifier: `tests/examples.rs` pins its digest.
