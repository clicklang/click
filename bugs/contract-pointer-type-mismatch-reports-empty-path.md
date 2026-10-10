# Contract pointer type mismatch reports an empty lowering path

A contract equality between different native pointee types reaches the kernel's
pointer type compatibility refusal, but the diagnostic says that lowering
produced zero paths. Report the unsupported comparison and its operand types;
an internal path count does not explain how to correct the contract.

Reproduced with `click verify probe.click`:

```c
// probe.c
unsigned char *probe(unsigned int *p, unsigned char *q) { return q; }
```

```click
verifying "probe.c";
uint8* probe(uint32* p, uint8* q) {
    ensures result == p;
} by { execute(); simp(); }
```

The current error ends with `could not lower fixed-state obligation: the kernel
lowering produced 0 paths, not one`. The same refusal occurs for a C++ function
that returns `reinterpret_cast<std::byte*>(p)` through the authenticated importer.

Acceptance: preserve the supported pointer-comparison semantics, diagnose the
incompatible `uint8*` and `uint32*` operands at the claim, and cover ordinary,
expanded and retained verification without raw internal path-count errors.
This diagnostic fix does not decide which pointer casts contracts should admit.
