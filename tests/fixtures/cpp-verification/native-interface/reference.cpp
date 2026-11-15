int& identity(int& value) noexcept { return value; }
int probe() noexcept {
    int value;
    int& alias = identity(value);
    alias = 7;
    return value;
}
