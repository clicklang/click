// Logical state of a dynamic std::span<int> descriptor. The resource
// records the backing address and count without granting backing authority.
abstract resource span_state(span: uint8*) {
    field data: int32*;
    field count: uint64;
}
