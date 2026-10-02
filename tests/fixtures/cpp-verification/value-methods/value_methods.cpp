struct FeeFrac {
    long fee;
    int size;
    bool IsEmpty() const noexcept { return size == 0; }
    void operator+=(const FeeFrac& other) noexcept {
        fee += other.fee;
        size += other.size;
    }
    template<class T> T unused(T value) { return value.unsupported(); }
};

int double_size(FeeFrac& value, int& untouched) noexcept {
    value += value;
    return value.size;
}

int double_size_direct(FeeFrac& value, int& untouched) noexcept {
    value.operator+=(value);
    return value.size;
}
