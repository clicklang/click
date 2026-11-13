// `std::as_writable_bytes(std::span<T>)`: the same storage viewed as bytes.
// The byte view keeps the backing address, as `uint8 *`, and has
// `sizeof(T)` bytes per element; it reads and grants nothing. Its argument
// is a span passed by value, so the result is stated from the argument as
// it was on entry.
//
// The function template is `as_writable_bytes<T, N>`, `N` its argument's
// extent, and an instance is named by both: `as_writable_bytes<int,
// 18446744073709551615>`. It is written out at each instance a call names
// that the C++ importer's name table states: element `int` and dynamic
// extent, `std::dynamic_extent`.
template<class T, std::size_t N> extern std::span<std::byte> std::as_writable_bytes<T, N>(std::span<T> s) {
    ensures std_span_data(result) == old(std_span_data(s) as (uint8 *));
    ensures std_span_size(result) == old(std_span_size(s)) * sizeof(T);
}
