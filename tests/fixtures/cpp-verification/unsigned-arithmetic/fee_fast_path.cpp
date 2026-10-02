// Synthetic fixture: these are EvaluateFee's exact unsigned fast-path expressions.
// Return the unsigned intermediate; upstream returns int64_t, whose uint64-to-int64
// conversion remains outside this slice.
unsigned long down(long fee, int at_size, int size) noexcept {
    return (static_cast<unsigned long>(fee) * at_size) / static_cast<unsigned int>(size);
}
unsigned long up(long fee, int at_size, int size) noexcept {
    return (static_cast<unsigned long>(fee) * at_size + size - 1U) / static_cast<unsigned int>(size);
}
