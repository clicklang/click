// Preserve the field width and short-circuit selector from the Bitcoin caller.
struct Box { long fee; };
int choose(const Box& box) noexcept {
    if (box.fee >= 0 && box.fee < 0x200000000) { return 1; }
    return 2;
}
