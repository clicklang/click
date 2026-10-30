// Resource descriptors name logical regions; these parameters carry no ownership.
theorem restrict(A: Resource, B: Resource, a: Resource, b: Resource) {
    requires separate(A, B);
    requires contains(A, a);
    requires contains(B, b);
    ensures separate(a, b);
}
