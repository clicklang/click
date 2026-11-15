struct Pair { int unused; int used; };
int take(Pair value) noexcept { return value.used; }
int probe(Pair& source) noexcept { return take(source); }
