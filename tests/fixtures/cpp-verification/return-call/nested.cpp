int echo(int value) noexcept { return value; }
long echo64(long value) noexcept { return value; }
unsigned echo_u32(unsigned value) noexcept { return value; }
unsigned long echo_u64(unsigned long value) noexcept { return value; }
bool echo_bool(bool value) noexcept { return value; }
int nested(int value) noexcept { return echo(echo(echo(value))); }
long nested64(long value) noexcept { return echo64(echo64(value)); }
unsigned nested_u32(unsigned value) noexcept { return echo_u32(echo_u32(value)); }
unsigned long nested_u64(unsigned long value) noexcept { return echo_u64(echo_u64(value)); }
bool nested_bool(bool value) noexcept { return echo_bool(echo_bool(value)); }
int collision(int __click_cpp_nested_value_0, int __click_cpp_nested_value_1) noexcept {
    return echo(echo(echo(__click_cpp_nested_value_0)));
}
long outer32(int value) noexcept { return long(value); }
long choose(bool first, int value) noexcept {
    if (first) return outer32(echo(value));
    else return echo64(echo64(long(value)));
}
