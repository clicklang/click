using U32 = unsigned;
using U64 = unsigned long;
using U128 = unsigned __int128;
int signed32(int n) noexcept { return int{n}; }
long signed64(long n) noexcept { return long{n}; }
U32 unsigned32(U32 n) noexcept { return U32{n}; }
U64 unsigned64(U64 n) noexcept { return U64{n}; }
__int128 signed128(__int128 n) noexcept { return __int128{n}; }
U128 unsigned128(U128 n) noexcept { return U128{n}; }
long widen(int n) noexcept { long value{n}; return value; }
bool truth() noexcept { return bool{1}; }
long constant() noexcept { return long{2147483648L}; }

// Matches the selected upstream Mul body; the wrapper tests modular composition.
struct FeeFrac {
    static inline __int128 Mul(long a, int b) noexcept {
        return __int128{a} * b;
    }
};
__int128 relay(long a, int b, int& untouched) noexcept {
    return FeeFrac::Mul(a, b);
}
long identity(long n) noexcept { return n; }
long argument(int n) noexcept { return identity(long{n}); }
int guarded(int n) noexcept { __builtin_assume(bool{n > 0}); return int{n}; }
