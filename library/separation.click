// Resource descriptors name logical regions; these parameters carry no ownership.
theorem restrict(A: Resource, B: Resource, a: Resource, b: Resource) {
    requires separate(A, B);
    requires contains(A, a);
    requires contains(B, b);
    ensures separate(a, b);
}

// Unequal indices describe disjoint complete elements, including padding.
theorem elements<T>(p: T*, i: uint64, j: uint64) {
    requires i != j;
    ensures separate(memory(p[i]), memory(p[j]));
}

// Bounds are in elements of T, not bytes. Descriptors grant no ownership.
theorem subrange<T>(p: T*, lo: int32, hi: int32, inner_lo: int32, inner_hi: int32) {
    requires lo <= inner_lo;
    requires inner_lo <= inner_hi;
    requires inner_hi <= hi;
    ensures contains(memory(p[lo..hi]), memory(p[inner_lo..inner_hi]));
}
