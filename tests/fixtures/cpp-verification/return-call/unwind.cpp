struct Restore {
    int* p;
    int saved;
    explicit Restore(int* slot) noexcept : p(slot), saved(*slot) { *p = 9; }
    ~Restore() noexcept { *p = saved; }
};
int helper(bool should_throw) {
    if (should_throw) { throw 7; }
    return 5;
}
int escaping(int& value, bool should_throw) {
    Restore guard(&value);
    return helper(should_throw);
}
int caught(int& value, bool should_throw) {
    try {
        Restore guard(&value);
        return helper(should_throw);
    }
    catch (int payload) { return value; }
}
int caught_value(int& value) {
    try {
        Restore guard(&value);
        return value;
    } catch (int payload) { return value; }
}
