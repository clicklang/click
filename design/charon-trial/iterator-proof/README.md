# Original shared byte iteration proof through Charon

`rust-iterators/sum.rs` and `frozen.click` are byte-identical copies of the
original `examples/rust-iterators` fixture. The migrated `sum.click` retains
every signature, specification function, precondition, and postcondition.
The native Charon artifact and import lock support offline checks.

The original body sums every byte through implicit shared slice iteration.
The proof relates the actual iterator cursor and remaining length to the
input prefix, proves a mathematical integer sum, and bounds every checked
signed addition. The original bound and viewed byte range include empty
inputs and arbitrary byte values; no input values or source body are changed.

The proof uses source `byte`/`total` locals, named iteration/read/addition
snapshots, and `loop(0)`, `read(0)`, `assignment(total, 1)`, and `back_edge()`
frontiers. It contains no MIR IDs, generated processed count, or compiler
statement indices. Invariant/ranking closure remains explicit.

Tests compare the source and frozen sidecar byte-for-byte and compare parsed
contracts. They reject missing views, a false sum, and a nondecreasing measure;
verify/profile agree, the complete expansion rechecks, and focused audits
check the read, assignment, and back-edge certificates. The live parity sweep
reextracts the unchanged source and verifies the port separately from the
frozen sidecar's recorded gap.

This checkpoint advances proof-port coverage to 15/16. The explicit
`rust-iter-references` proof is still a separate port; no new result for that
fixture is claimed here.
