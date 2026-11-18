struct Widget { int sibling; int value; };
struct Outer {
    int first;
    Widget child;
    Widget& get() noexcept { return child; }
    const Widget& peek() const noexcept { return child; }
};
int probe(Outer& outer) noexcept {
    outer.get().value = outer.first;
    return outer.peek().value;
}
