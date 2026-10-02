// Concrete helper instances, selected through ordinary source callers.
template<bool First>
int choose(int a, int b) noexcept {
    if constexpr (First) {
        return a;
    } else {
        return b;
    }
}
int both(int a, int b, int* untouched) noexcept {
    int first = choose<true>(a, b);
    int second = choose<false>(a, b);
    return first + second;
}

template<typename T>
T identity(T value) noexcept { return value; }
unsigned long widths(int a, unsigned long b) noexcept {
    int small = identity<int>(a);
    unsigned long wide = identity<unsigned long>(b);
    return static_cast<unsigned long>(small) + wide;
}

struct Value {
    long fee;
    template<bool TakeFee>
    long select() const noexcept {
        if constexpr (TakeFee) { return fee; }
        else { return 0L; }
    }
};
long member(const Value& value) noexcept {
    long selected = value.select<true>();
    long zero = value.select<false>();
    return selected + zero;
}

int unavailable(int) noexcept;
template<bool Supported>
int bounded(int value) noexcept {
    if constexpr (Supported) { return value; }
    else { return unavailable(value); }
}
int accepted(int value) noexcept {
    int result = bounded<true>(value);
    return result;
}
int rejected(int value) noexcept {
    int result = bounded<false>(value);
    return result;
}

unsigned long exact_types(unsigned long a, unsigned long long b) noexcept {
    unsigned long first = identity<unsigned long>(a);
    unsigned long long second = identity<unsigned long long>(b);
    return first + second;
}
constexpr bool constant_evaluation() noexcept { return __builtin_is_constant_evaluated(); }
int constant_context() noexcept {
    if constexpr (constant_evaluation()) { return 1; }
    else { return 2; }
}
int discarded_without_else(int value) noexcept {
    if constexpr (false) { unavailable(value); }
    return value;
}
int runtime_if(int value) noexcept {
    if (true) { return value; }
    else { return unavailable(value); }
}
template<bool Flag>
int flag() noexcept { return Flag; }
int get_flag() noexcept {
    int result = flag<true>();
    return result;
}

// Preserve EvaluateFee's instantiated unsigned fast-path expressions. The
// unsigned return keeps the still-unsupported final int64 conversion explicit.
template<bool RoundDown>
unsigned long fee_fast_path(long fee, int at_size, int size) noexcept {
    if constexpr (RoundDown) {
        return (static_cast<unsigned long>(fee) * at_size) / static_cast<unsigned int>(size);
    } else {
        return (static_cast<unsigned long>(fee) * at_size + size - 1U) / static_cast<unsigned int>(size);
    }
}
unsigned long fee_down(long fee, int at_size, int size) noexcept {
    unsigned long result = fee_fast_path<true>(fee, at_size, size);
    return result;
}
unsigned long fee_up(long fee, int at_size, int size) noexcept {
    unsigned long result = fee_fast_path<false>(fee, at_size, size);
    return result;
}
