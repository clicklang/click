struct Restore {
    int* p;
    int saved;

    explicit Restore(int* slot) noexcept : p(slot), saved(*slot) {
        *p = 7;
    }

    ~Restore() noexcept {
        *p = saved;
    }
};

int construction_prefix(bool early, int& value) noexcept {
    Restore first(&value);
    if (early) {
        return value;
    }
    Restore second(&value);
    value = 9;
    return value;
}

int before_construction(bool early, int& value) noexcept {
    if (early) {
        return value;
    }
    Restore state(&value);
    return value;
}
