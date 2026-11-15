#include <span.h>

unsigned long length(std::span<std::byte> view) noexcept {
    return view.size();
}

unsigned int probe() noexcept {
    unsigned int obj;
    std::span<std::byte> dst(reinterpret_cast<std::byte*>(&obj), 4);
    return length(dst);
}
