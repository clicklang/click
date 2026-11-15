#include <span.h>

void fill(std::byte* p) noexcept {
    p[0] = static_cast<std::byte>(120);
    p[1] = static_cast<std::byte>(86);
    p[2] = static_cast<std::byte>(52);
    p[3] = static_cast<std::byte>(18);
}

unsigned int probe() noexcept {
    unsigned int obj;
    fill(reinterpret_cast<std::byte*>(&obj));
    return obj;
}
