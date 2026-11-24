# Model C++ exceptions with class types and exceptional resources

Priority: P2.

Soundness: incomplete. No false acceptance is known. Unsupported exception
forms are refused at import: handlers other than one by-value
`catch (int name)`, catch-all and class-typed handlers, user constructors,
lvalue throws, nontrivial exception classes, resource transitions with
`throws`, and general unwinding
([supported C++](../docs/reference/cli/capture.md)). The delivered forms are
checked on both exits against their declared footprint.

## Status

Delivered: `throws int32`, exact opaque `throws std::ios_base::failure`, and
`throws T` for trivial user aggregates, each with borrowed `owns`/`views` on
both exits; checked `noexcept`; allocation-failure termination as a
documented trust assumption; and the unchanged Bitcoin `SpanReader::ignore`,
`SpanReader::read` and `ser_readdata32<SpanReader>` with normal and
exceptional contracts, expansion and retained-session replay
(`integrations/bitcoin-core-money-range/`). Remaining: typed handlers,
design choice 4 below.

## Motivation

Bitcoin Core reports malformed input by throwing. The bounded cursor
`SpanReader` in `src/streams.h` (Bitcoin v31.1, commit
`9be056a8a72b624dae9623b2f7bded92c2a21c91`, SHA-256
`71b243c0614d41b60b8d0b2b6c14b7f2795412d80db129cef446af57e4e88ab8`)
is the selected first target of the bounded-bytes slice in
[cpp-support.md](cpp-support.md):

```cpp
void read(std::span<std::byte> dst)
{
    if (dst.size() == 0) {
        return;
    }
    if (dst.size() > m_data.size()) {
        throw std::ios_base::failure("SpanReader::read(): end of data");
    }
    memcpy(dst.data(), m_data.data(), dst.size());
    m_data = m_data.subspan(dst.size());
}
```

`ignore(n)`, the `ser_readdata8/16/32/64` helpers in `serialize.h`, and
`ReadCompactSize` all propagate or throw the same exception. A contract that
excludes the throwing path by precondition would leave the actual
malformed-input behavior unverified, so the exception has to be modeled.

The first slice now supports memory footprints on both exits and an opaque
`std::ios_base::failure` payload; see
[architecture](../docs/internals/architecture.md#selected-control-flow-and-c-cleanup-model)
and [the language reference](../docs/reference/language/index.md#exceptional-results).
Handlers still match only `catch (int name)`; Bitcoin callers need
`const std::ios_base::failure&` or `const std::exception&`, which is the
remaining application target below.

## Violated invariant

A C++ function that throws a standard-library exception class while holding
caller memory has a checked contract for both outcomes: what it returns and
changes on normal exit, and what it throws and changes on exceptional exit.
The caller gets back exactly the authority it lent on either exit.

## Design

The user accepted these choices on 2026-10-13.

**1. Exceptional exits keep the memory footprint.** A `throws` function may
have `owns` and `views` clauses. They hold on both exits: on a throw, the
caller receives exactly the resources it lent, as on a return.
`exceptional ensures` may then name memory and `old(...)`. A function may
change memory before throwing; its `exceptional ensures` must describe what
changed, as a normal postcondition does. `consumes`, `produces` and
`constructs` combined with `throws` stay refused until a selected program
needs a different exceptional footprint. The kernel already keeps returned
and thrown states separate; the change is to check the exit footprint and
frame at the exceptional exit as it is checked at a return. This part is
language-neutral.

**2. Class-typed exceptions are opaque values of an exact type.**
`throws int32` generalizes to `throws T`. For a standard-library exception
class, `exception` is an opaque value: the contract fixes its exact dynamic
type, and proofs cannot read its message or call `what()`. Constructing one
(`std::ios_base::failure(const char*)`) is a standard-library catalog
entry. Its effect is a fresh exception of that type and nothing a proof can
observe. The object belongs to the C++ runtime, not to the proof's resources,
and its library destructor is trusted.

**3. Allocation failure while constructing an exception is a profile
assumption.** The message string inside `ios_base::failure` is allocated, so
its construction can throw `std::bad_alloc`. Bitcoin Core installs a
new-handler that terminates on allocation failure, so `bad_alloc` never
propagates in bitcoind. The selected profile records "allocation failure
terminates" as an explicit assumption in
[trust](../docs/concepts/trust.md), and signatures do not list
`std::bad_alloc`. A program run without that new-handler is outside the
profile.

**4. Handlers match by type (needed once a verified caller catches).**
This covers `catch (const T&)` by exact type or public unambiguous base
class, taken from Clang's class hierarchy; `catch (...)`; source-order
handler selection; and propagation of an unmatched exception outward. The
exception object's lifetime ends when its handler exits. An exception that
would escape a `noexcept` function remains a proof obligation: the proof
must show it cannot happen.

Out of scope: rethrow, `std::exception_ptr`, user-defined exception classes
with nontrivial members, throwing constructors or destructors of guards,
and exceptions crossing threads.

## Intended regression

Through a fixture harness that is identified separately from Bitcoin source,
the pinned input closure gains `src/streams.h` and its includes. Then:

- Delivered: `SpanReader::ignore` and `SpanReader::read` verify unchanged with
  contracts for both outcomes. On a normal exit the bytes are copied and the
  cursor advances. On an exceptional exit the exception is exactly
  `std::ios_base::failure`, `old(size) < n`, and the reader and destination
  are unchanged.
- Delivered: `ser_readdata32(SpanReader&)` verifies, returning the
  little-endian value of the four bytes on the pinned x86-64 target and
  propagating the reader's exception.
- Remaining: a Click-checked caller catches `const std::ios_base::failure&`, and another
  catches `const std::exception&`.

## Acceptance criteria

- A `throws` contract with `owns` and `views` verifies in C and in C++. Both
  exits are checked against the declared footprint. A change before a throw
  that `exceptional ensures` does not describe is refused, as is a throw
  that keeps or leaks authority.
- `throws std::ios_base::failure` imports from the pinned Clang profile. A
  false exceptional type, a false claim about the exceptional state, and a
  proof that reads the opaque payload are each refused.
- The profile assumption about allocation failure is documented in the trust
  document and recorded in the import profile.
- Remaining: type-matched handlers verify for exact and base-class
  `catch (const T&)` and for `catch (...)`. An unmatched exception
  propagates, an exception escaping `noexcept` is refused, and handler order
  is respected. [Supported C++](../docs/reference/cli/capture.md) then drops
  the `catch (int name)`-only restriction.
- The `SpanReader` regressions above verify, expand and reverify, with
  refusals for an out-of-bounds read claimed to return normally, a missing
  destination ownership, and a false decoded value.
- Done: exceptional-exit footprint checks scale with unrelated context, in
  `src/scaling_tests/surface/tests/scaling_tests.rs`
  (`exceptional_borrowed_memory_is_indexed_in_unrelated_context`,
  `exceptional_cleanup_edges_scale_near_linearly_with_unrelated_context`).
- [Supported C++](../docs/reference/cli/capture.md) and the language
  reference describe the new boundary, and
  [cpp-support.md](cpp-support.md) points here for the bounded-bytes slice.
