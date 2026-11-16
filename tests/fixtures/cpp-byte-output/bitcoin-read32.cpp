#include <serialize.h>
struct FixtureReader {
    const std::byte* data;
    unsigned long remaining;
    void read(std::span<std::byte> dst) noexcept {
        dst[0] = data[0];
        dst[1] = data[1];
        dst[2] = data[2];
        dst[3] = data[3];
        data = data + 4;
        remaining = remaining - 4;
    }
};
uint32_t probe(FixtureReader& stream) { return ser_readdata32(stream); }
