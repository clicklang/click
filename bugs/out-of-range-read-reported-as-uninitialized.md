# An out-of-range read is reported as an uninitialized read

## Violated invariant

A refusal should name the actual reason. A read one past an initialized local
array (`int32 values[4] = {1,2,3,4}; … if (0 <= x && x < 5) r = values[x];`)
is refused with "read of uninitialized storage" rather than as an access
outside `values`. That is sound, but misleading: the uninitialized check runs
before the bounds obligation. The negative mdtest
`a_symbolic_read_one_past_an_initialized_local_array_is_refused.md` (PR #53)
pins the misleading text.

## Intended regression

Change that mdtest's expectation to the bounds wording (as PR #36 prints for
stores: "may read outside `values`: could not show `0 <= x && x < 4` …"), and
add a global and a heap variant.

## Acceptance criteria

- A read that may fall outside its object is refused for the bounds, naming
  the index bound it could not show, before any initialization check.
- A read inside the object of bytes never written is still reported as
  uninitialized.
