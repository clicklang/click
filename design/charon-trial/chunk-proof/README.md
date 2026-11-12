# Original chunks_exact proof through Charon

`chunks.rs` is a byte-identical copy of the original
`examples/rust-chunks-exact` source, and `frozen.click` archives its original
sidecar, respelled once in today's syntax with its contract and proof
unchanged (`../README.md`, Complete canonical proof-port adoption). `chunks.click` preserves its full contract
and is the example's current proof: the iterator is a value of the library's `ChunksExact` and the proof
cites its contract (`examples/rust-chunks-exact/README.md`).
The native Charon artifact and import lock are committed for offline checks.

The loop covers every full four-byte chunk; the returned remainder length is
`bytes_len % 4`, and every input byte is preserved. Empty inputs, exact
multiples, and short tails are included. Existing importer tests retain zero
chunk-size rejection.

Run `click verify design/charon-trial/chunk-proof/chunks.click`. Locked tests
check verify/profile/audit and expansion rechecking. The live parity sweep
reextracts the original source, verifies the port, and records the frozen
sidecar's existing proof gap separately.
