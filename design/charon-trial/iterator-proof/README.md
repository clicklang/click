# Original shared byte iteration proof through Charon

Each directory mirrors the corresponding example's original Rust source and
its verified `sum.click` proof. Earlier sidecars that used generated
iterator and checked-operand locals are preserved in Git history. The native
Charon artifacts and import locks support offline checks.

The original body sums every byte through implicit shared slice iteration.
The proof relates the iterator's remaining length, `iter.len()`, to the
input prefix, proves a mathematical integer sum, and bounds every checked
signed addition. The original bound and viewed byte range include empty
inputs and arbitrary byte values; no input values or source body are changed.

The proof uses source `byte`/`total` locals, named iteration/read/addition
states, and `loop(0)`, `read(0)`, `assignment(total, 1)`, and `back_edge()`
frontiers. It contains no MIR IDs, generated processed count, or compiler
statement indices. Invariant/ranking closure remains explicit.

Tests reject missing views, a false sum, and a nondecreasing measure.
Verification and profiling agree, the complete expansion rechecks, and
focused audits check the read, assignment, and back-edge certificates.

`rust-iter-references` uses an explicit `for byte in bytes.iter()`. Its proof
names the checked byte read with `let { result: loaded_byte } = step();` and
keeps that value as compiler temporaries leave scope. Both proofs retain the
full mathematical sum contract.
