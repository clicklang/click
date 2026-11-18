
struct Widget { int value; };
struct Outer { int first; Widget child; Widget& get() noexcept { return child; } };
Widget& child(Outer& outer) noexcept { return outer.get(); }
int probe(Outer& outer, int value) noexcept { auto& ref = child(outer); ref.value = value; return outer.child.value; }
