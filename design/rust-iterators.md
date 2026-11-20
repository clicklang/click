# Rust iterator representation

Imported iterators retain the Rust fields their code operates on.
`ChunksExact` holds `v`, `rem`, and `chunk_size`. A slice iterator holds
the remaining slice, `Enumerate` holds its iterator and count, and `Range`
holds `start` and `end`. A crate-defined iterator runs its own `next`
under its checked contract. A loop proof can name the iterator's fields with
`iter.<field>` and `loop(i).iter.<field>`.

The Rust reference describes the supported
[chunk loops](../docs/reference/rust.md#exact-chunk-iterators-and-remainder) and
[crate iterators](../docs/reference/rust.md#crate-iterators). See the
[chunk example](../examples/rust-chunks-exact/) and
[slice iterator example](../examples/rust-iter-references/) for checked proofs.

The retired abstract iterator models, proof observations, and importer
migration plan are recorded in [Git history](https://github.com/clicklang/click/blob/f25b570397/design/rust-iterators.md).
The [adler2 trial](adler32/project/adler2/README.md) tracks the remaining proofs
that still refer to the retired model.
