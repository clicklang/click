#include <span>

bool is_empty(std::span<int> span) noexcept {
    return span.empty();
}

bool probe(const std::span<int>& source) noexcept {
    return is_empty(source);
}
