int echo(int value) noexcept { return value; }
long echo64(long value) noexcept { return value; }
unsigned int echo_u32(unsigned int value) noexcept { return value; }
unsigned long echo_u64(unsigned long value) noexcept { return value; }
bool echo_bool(bool value) noexcept { return value; }
int relay(int value, int* untouched) noexcept { return echo(value); }
long relay64(long value) noexcept { return (echo64(value)); }
unsigned int relay_u32(unsigned int value) noexcept { return echo_u32(value); }
unsigned long relay_u64(unsigned long value) noexcept { return echo_u64(value); }
bool relay_bool(bool value) noexcept { return echo_bool(value); }
int choose(bool first, int value) noexcept {
    if (first) { return echo(value); }
    return echo(7);
}
// Synthetic fast-path prerequisites. The upstream Assume and __int128 path
// remain unsupported; preserve the method-template return-call wrapper shape.
struct FeeFrac {
    long fee;
    int size;
    template<bool RoundDown>
    long EvaluateFee(int at_size) const noexcept {
        if constexpr (RoundDown) {
            return (static_cast<unsigned long>(fee) * at_size) / static_cast<unsigned int>(size);
        } else {
            return (static_cast<unsigned long>(fee) * at_size + size - 1U) / static_cast<unsigned int>(size);
        }
    }
    long EvaluateFeeDown(int at_size) const noexcept { return EvaluateFee<true>(at_size); }
    long EvaluateFeeUp(int at_size) const noexcept { return EvaluateFee<false>(at_size); }
};
