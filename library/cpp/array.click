// `std::array<T, N>`: `N` elements held in the object, named by the model
// accessor `std_array_data(a)`. The extent is the template argument, so an
// instance states it as a literal, `4u64`. The element accessors have a
// `const` and a mutable overload, each written as its own template method:
// an instance is written from the overload whose receiver constness it
// has. They require an index inside the array and form an address without
// reading it.
//
// Each method is written out at each element type and extent a call names;
// the element types are the C++ importer's `SPAN_ELEMENTS` without `const`,
// and an extent is written out only when its byte size fits a `uint64`.
template<class T, std::size_t N> extern unsigned long std::array<T, N>::size() const {
    ensures result == N;
}
template<class T, std::size_t N> extern T* std::array<T, N>::data() {
    ensures result == &std_array_data(this)[0];
}
template<class T, std::size_t N> extern const T* std::array<T, N>::data() const {
    ensures result == &std_array_data(this)[0];
}
template<class T, std::size_t N> extern T& std::array<T, N>::operator[](unsigned long index) {
    requires index < N;
    ensures &result == &std_array_data(this)[index];
}
template<class T, std::size_t N> extern const T& std::array<T, N>::operator[](unsigned long index) const {
    requires index < N;
    ensures &result == &std_array_data(this)[index];
}
template<class T, std::size_t N> extern T& std::array<T, N>::front() {
    requires 1u64 <= N;
    ensures &result == &std_array_data(this)[0];
}
template<class T, std::size_t N> extern const T& std::array<T, N>::front() const {
    requires 1u64 <= N;
    ensures &result == &std_array_data(this)[0];
}
template<class T, std::size_t N> extern T& std::array<T, N>::back() {
    requires 1u64 <= N;
    ensures &result == &std_array_data(this)[N - 1u64];
}
template<class T, std::size_t N> extern const T& std::array<T, N>::back() const {
    requires 1u64 <= N;
    ensures &result == &std_array_data(this)[N - 1u64];
}
