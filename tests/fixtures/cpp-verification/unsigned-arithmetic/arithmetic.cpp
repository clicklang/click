unsigned long maximum() noexcept { return 18446744073709551615UL; }
unsigned long add64(unsigned long a, unsigned long b) noexcept { return a + b; }
unsigned long sub64(unsigned long a, unsigned long b) noexcept { return a - b; }
unsigned long mul64(unsigned long a, unsigned long b) noexcept { return a * b; }
unsigned long div64(unsigned long a, unsigned long b) noexcept { return a / b; }
unsigned long rem64(unsigned long a, unsigned long b) noexcept { return a % b; }
unsigned long neg64(unsigned long a) noexcept { return -a; }
unsigned int add32(unsigned int a, unsigned int b) noexcept { return a + b; }
unsigned long signed_to_unsigned(int a) noexcept { return static_cast<unsigned long>(a); }
unsigned int narrow_unsigned(long a) noexcept { return static_cast<unsigned int>(a); }
int narrow_signed(unsigned long a) noexcept { return static_cast<int>(a); }
long widen_unsigned(unsigned int a) noexcept { return a; }
bool truth(unsigned long a) noexcept { return bool(a); }
unsigned long relay(unsigned long a, unsigned long b, int& untouched) noexcept {
    unsigned long captured = add64(a, b);
    return captured;
}
unsigned long mixed(long a, unsigned int b) noexcept { return a + b; }
