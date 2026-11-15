#include <span.h>

void fill(std::span<std::byte> dst) noexcept {
    dst[0] = static_cast<std::byte>(120);
    dst[1] = static_cast<std::byte>(86);
    dst[2] = static_cast<std::byte>(52);
    dst[3] = static_cast<std::byte>(18);
}

unsigned int probe() noexcept {
    unsigned int obj;
    std::span<std::byte> dst(reinterpret_cast<std::byte*>(&obj), 4);
    fill(dst);
    return obj;
}
