# Read-only wide-index refusal invents a source store

## Violated invariant

A proof diagnostic must describe an actual source effect. A prompt smart-tactic
failure is allowed, but input-resource materialization must not be described as
a store performed by a read-only function. Nor should the suggested repair
contradict a known precondition.

## Reproduction and intended regression

Put these fences in a standalone Markdown fixture and run `click verify`:

```c filename=last.c
int32 last(int32* data, uint64 length) {
    return *(data + (length - 1ULL));
}
```

```click
verifying "last.c";
int32 last(int32* data, uint64 length) {
    owns data[0..1];
    requires length == 1u64;
    ensures result == old(data[0]);
} by { execute(); simp(); }
```

Reproduced through the plain C0 CLI and independently through a C++ import of
the same read-only operation. Both refusals say:

```text
`data[(length - 1u64)]` may have changed since earlier in this function:
the store to `data[0]` may have written it.
If `(length - 1u64)` and `0` differ, state `(length - 1u64) != 0`.
```

There is no source store. The premise `length == 1u64` actually implies index
zero, so the proposed inequality is false. Explicitly rewriting that premise
before `simp` verifies the C++ regression without changing its source. This
bug concerns the explanation, not a requirement to make smart search complete.
Investigate the resource tracker's interpretation of initial cell/snapshot
materialization and the diagnostic's attribution of `Change::Store`.

## Acceptance

- A focused regression rejects invented source-store attribution for this
  read-only shape, including the C++ route.
- If `simp` still refuses, the bounded diagnostic identifies the unresolved
  index/address equality without suggesting the false inequality.
- Actual intervening source stores retain useful alias/frame explanations.
- The explicit rewrite proof continues to verify normally and through expanded
  and retained checking. Do not expand the failing smart tactic.
