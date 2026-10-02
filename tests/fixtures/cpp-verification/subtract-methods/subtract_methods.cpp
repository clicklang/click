struct FeeFrac {
    long fee;
    int size;
    void operator-=(const FeeFrac& other) noexcept {
        fee -= other.fee;
        size -= other.size;
    }
};

int clear_value(FeeFrac& value, int& untouched) noexcept {
    value -= value;
    return value.size;
}
