# An offset from a pointer-valued library result read at a mark has no pointee type

Soundness: incomplete. A true fact cannot be stated in one of its natural
spellings; nothing false is accepted.

`at(mark, f(x).as_ptr()) + 1u64`, where `f(x).as_ptr()` is a pointer the
Click library's `slice::as_ptr` returns, is refused when lowered: "a pointer
operation has no known pointee type". The same value written with the mark
inside, `at(mark, f(x)).as_ptr() + 1u64`, lowers and proves. The pointee
type is the function's declared result type in both.

Invariant: a pointer-typed expression keeps its pointee type through
`at(...)`, as a C pointer read at a mark does.

## Reproduction

`design/charon-trial/slice-iter/sum.click`. After
`step_until(assignment(byte, 0));` in the loop's `preserve`, add:

```click
have iter.as_slice().as_ptr() == at(iteration, iter.as_slice().as_ptr()) + 1u64;
```

```text
could not lower `have` proposition
the kernel lowering produced no path
every evaluation path ended in a runtime error
a pointer operation has no known pointee type
```

With the mark moved inside the method call the same fact verifies:

```click
have iter.as_slice().as_ptr() == at(iteration, iter.as_slice()).as_ptr() + 1u64;
```

Run the nightly test
`charon_slice_iter_sums_bytes_by_its_library_contract` with the line added,
or `click verify design/charon-trial/slice-iter/sum.click` with a pinned
Charon.

A theorem over a `Slice<uint8>` parameter does not reproduce it:
`slice::as_ptr(s) + 1u64 == p + 1u64` verifies there.

## Acceptance criteria

- The first `have` above lowers and verifies.
- An mdtest or nightly regression states an offset from
  `at(mark, <pointer-valued library call>)` for a byte and a wider element.
