struct Restore {
    int* p;
    int saved;
    explicit Restore(int* slot) noexcept : p(slot), saved(*slot) { *p = 7; }
    ~Restore() noexcept { *p = saved; }
};
int read(int* slot) noexcept { return *slot; }
long wide() noexcept { return 4294967303L; }
bool is_seven(int* slot) noexcept { return *slot == 7; }
int capture(int& value) noexcept {
    Restore guard(&value);
    return read(&value);
}
long capture_wide(int& value) noexcept {
    Restore guard(&value);
    return wide();
}
bool capture_bool(int& value) noexcept {
    Restore guard(&value);
    return is_seven(&value);
}
long ordinary_wide(int& value) noexcept {
    Restore guard(&value);
    return 4294967303L;
}
bool ordinary_bool(int& value) noexcept {
    Restore guard(&value);
    return true;
}
int echo(int value) noexcept { return value; }
int capture_nested(int& value) noexcept {
    Restore guard(&value);
    return echo(read(&value));
}
