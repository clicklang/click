# Original chunks_exact proof through Charon

`chunks.rs` and `frozen.click` are byte-identical copies of the original
`examples/rust-chunks-exact` fixture. `chunks.click` preserves its full contract
and adapts only the proof to the actual iterator storage and checked frontiers.
The native Charon artifact and import lock are committed for offline checks.

The loop covers every full four-byte chunk; the returned remainder length is
`bytes_len % 4`, and every input byte is preserved. Empty inputs, exact
multiples, and short tails are included. Existing importer tests retain zero
chunk-size rejection. This port adds no generated processed count.

`execute_until(loop(0))`, `execute_until(read(1))`, and
`execute_until(back_edge())` replace compiler statement counts. The last
selector finishes only the current preservation region via checked steps.
It grants no invariant or termination authority; `close_invariants()` remains
required. Explicit branches must be proved separately.

Run `click verify design/charon-trial/chunk-proof/chunks.click`. Locked tests
check verify/profile/audit and expansion rechecking. The live parity sweep
reextracts the original source, verifies the port, and records the frozen
sidecar's existing proof gap separately.
