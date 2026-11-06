// Resource descriptors name logical regions; these parameters carry no ownership.
theorem restrict(A: Resource, B: Resource, a: Resource, b: Resource) {
    requires separate(A, B);
    requires contains(A, a);
    requires contains(B, b);
    ensures separate(a, b);
}

// Unequal indices describe disjoint complete elements, including padding.
theorem elements<T, I>(p: T*, i: I, j: I) {
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

// Descriptor laws grant no ownership. Star retains both requirements.
theorem contains_refl(A: Resource) { ensures contains(A, A); }
theorem contains_trans(A: Resource, B: Resource, C: Resource) {
    requires contains(A, B);
    requires contains(B, C);
    ensures contains(A, C);
}
theorem contains_left(A: Resource, B: Resource) { ensures contains(A * B, A); }
theorem contains_right(A: Resource, B: Resource) { ensures contains(A * B, B); }
theorem separate_symm(A: Resource, B: Resource) {
    requires separate(A, B);
    ensures separate(B, A);
}
theorem separate_star(A: Resource, B: Resource, C: Resource) {
    requires separate(A, C);
    requires separate(B, C);
    ensures separate(A * B, C);
}
theorem separate_emp(A: Resource) { ensures separate(separation::emp, A); }

// A pure viewability fact restricts along explicitly proved containment.
theorem viewable_restrict(A: Resource, B: Resource) {
    requires viewable(A);
    requires contains(A, B);
    ensures viewable(B);
}
