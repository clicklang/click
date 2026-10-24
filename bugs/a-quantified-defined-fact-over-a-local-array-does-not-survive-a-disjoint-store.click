target "x86_64-unknown-linux-gnu";
mode "kernel";
verifying "a-quantified-defined-fact-over-a-local-array-does-not-survive-a-disjoint-store.c";
int32 d(int32 j) {
    ensures true;
} by {
    step();
    step();
    step();
    step();
    have forall (k: uint64) { 0u64 <= k and k < 1u64 implies tmp[k] != 0u8 } by { enumerate(); }
    have forall (k: uint64) { 0u64 <= k and k < 2u64 implies defined(tmp[k]) } by { enumerate(); }
    step();
    have forall (k: uint64) { 0u64 <= k and k < 1u64 implies tmp[k] != 0u8 } by { assumption(); }
    have forall (k: uint64) { 0u64 <= k and k < 2u64 implies defined(tmp[k]) } by { assumption(); }
    execute();
    simp();
}
