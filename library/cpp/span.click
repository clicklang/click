// `std::span<T>` with dynamic extent: a view of `[data, data + size)`, its
// state named by the model accessors `std_span_data` and `std_span_size`.
// The element accessors require an index inside the view, which the
// standard makes a precondition; they form an address and read nothing.
// The subview operations require the subview to lie inside the view, as the
// standard does, and keep the backing storage. `subspan`'s count
// `std::dynamic_extent`, 18446744073709551615u64, means "to the end".
//
// Each method is written out at each element type a call names, and its
// parameters take that instance's names; the element types are the C++
// importer's `SPAN_ELEMENTS`.
template<class T> extern unsigned long std::span<T>::size() const {
    views std_span_size(this);
    ensures result == std_span_size(this);
}
template<class T> extern unsigned long std::span<T>::size_bytes() const {
    views std_span_size(this);
    ensures result == std_span_size(this) * sizeof(T);
}
template<class T> extern T* std::span<T>::data() const {
    views std_span_data(this);
    ensures result == std_span_data(this);
}
template<class T> extern T& std::span<T>::front() const {
    views std_span_data(this);
    views std_span_size(this);
    requires 1u64 <= std_span_size(this);
    ensures &result == std_span_data(this);
}
template<class T> extern T& std::span<T>::back() const {
    views std_span_data(this);
    views std_span_size(this);
    requires 1u64 <= std_span_size(this);
    ensures &result == std_span_data(this) + (std_span_size(this) - 1u64);
}
template<class T> extern T& std::span<T>::operator[](unsigned long index) const {
    views std_span_data(this);
    views std_span_size(this);
    requires index < std_span_size(this);
    ensures &result == std_span_data(this) + index;
}
template<class T> extern std::span<T> std::span<T>::first(unsigned long count) const {
    views std_span_data(this);
    views std_span_size(this);
    requires count <= std_span_size(this);
    ensures std_span_data(result) == std_span_data(this);
    ensures std_span_size(result) == count;
}
template<class T> extern std::span<T> std::span<T>::last(unsigned long count) const {
    views std_span_data(this);
    views std_span_size(this);
    requires count <= std_span_size(this);
    ensures std_span_data(result) == std_span_data(this) + (std_span_size(this) - count);
    ensures std_span_size(result) == count;
}
template<class T> extern std::span<T> std::span<T>::subspan(unsigned long offset, unsigned long count) const {
    views std_span_data(this);
    views std_span_size(this);
    requires offset <= std_span_size(this);
    requires count != 18446744073709551615u64 implies count <= std_span_size(this) - offset;
    ensures std_span_data(result) == std_span_data(this) + offset;
    ensures count == 18446744073709551615u64 implies std_span_size(result) == std_span_size(this) - offset;
    ensures count != 18446744073709551615u64 implies std_span_size(result) == count;
}
