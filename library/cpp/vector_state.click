// Logical state of an existing std::vector<unsigned char>.
abstract resource vector_state(vector: const void*) {
    field length: uint64;
}
