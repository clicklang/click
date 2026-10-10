# `simp` cannot prove a wide `viewable` goal from the same bytes stated with a 32-bit bound

## Violated invariant

`viewable(bytes[0..3])` and `viewable(bytes[0..n])` with `n == 3u64` describe
the same bytes. `simp` proves the second from the first when `n` is `int32`,
but refuses it when `n` is `uint64` and says no viewable range over the base
was stated anywhere, although one was.

## Reproduction

```c
uint64 f(uint8 bytes[], uint64 n) {
    return 0;
}
```

```click
uint64 f(uint8 bytes[], uint64 n) {
    requires viewable(bytes[0..3]);
    requires n == 3u64;

    ensures result == 0u64 by {
        have viewable(bytes[0..n]) by {
            simp();
        }
        execute();
        simp();
    }
}
```

`simp` fails with "`viewable(bytes[0..n])` was not proved and no viewable
range over the same base was stated anywhere in scope, so there is nothing to
narrow".

A caller holding a constant 32-bit range cannot hand it to a `size_t`
consumer such as `strlen` without restating it; the C-string mdtests state
the wide form directly instead.

## Intended regression

An mdtest with the program above verifying, plus one with `n == 4u64` that
is still refused.

## Acceptance criteria

- The viewable-range narrowing step considers a stated 32-bit range when the
  goal's range is wide, comparing extents as unsigned 64-bit byte counts.
- The diagnostic names the stated range when it exists but does not cover
  the goal.
