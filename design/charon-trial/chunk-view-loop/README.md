# Shared subslice calls inside a stored chunk loop

`loop.rs` retains an ordinary stored `ChunksExact` iterator and passes its
shared subslices to a helper that reads the first byte. The locked native
Charon artifact retains that source and control flow. `loop.click` proves the
helper's read and a terminating loop over sixteen bytes, using the actual
iterator cursor and remaining count.

The regression exercises a symbolic loop head: its chunk pointer has a checked
alias to an offset within the original input view. Call planning must select
the original resource occurrence through the pointer index, validate its live
loan binding and byte coverage, and recover the parent view after the call.
An alias or viewability proposition alone cannot grant authority.

Normal tests verify the proof and reject missing views, an overlong child view,
a false cursor invariant, and a false result. Kernel tests check missing alias
and loan evidence, exact recovery, and deterministic scaling. Nightly tests
expand the proof and independently verify the resulting certificate, then
check profiling. This fixture does not prove Adler's checksum or cover arbitrary
input lengths, tails, or general initial checksum states.
